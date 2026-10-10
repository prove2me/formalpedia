-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability
-- status  : ACCEPTED   (disprove)
-- author  : @fabianroll
-- created : 2026-10-10T08:54:21.454526+00:00
-- url     : https://prove2.me/submissions/9b37504d-67da-4865-b8aa-2d87ebe83b59

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

open PersistClust.Count

/-!
# REFUTATION — `theorem_4_5_lemma_4_6_corrected_stability` is FALSE as stated.

⚠️ DO NOT SUBMIT as a solution. This file is a verified *counterexample*, NOT a solution. ⚠️

The child lemma states: for TWO GENUINE persistence modules (`rankFn` + `FiltrationLaw`)
whose TRUNCATED ranks satisfy the box-expansion inequalities with NO `α` guard (`hbox`),
there is a multi-bijection `δ : Copies (mult (truncRank rX α)) ≃ Copies (mult (truncRank rY α))`
moving every point by at most `ε` in `L∞` (both coordinates, both directions).

The statement is FALSE. The root cause: classes born at time `+∞` — points that lie in
`stage u` for EVERY real `u` — are INVISIBLE to `mult` (the guard `p.1 ≠ ⊤` in the
definition of `mult` kills every point `((⊤, d))`), yet they still inflate the truncated
rank functions. Two modules can carry ε-interleaved `⊤`-born class structure whose slack
absorbs an otherwise-unmatched finite bar of the other module. The paper (Appendix A)
never sees this because its modules are TAME — `𝔽^s` is EMPTY for all large `s`
(`IsTame0`, condition 3) — which precludes `⊤`-born classes. The Lean statement carries
only `FiltrationLaw`, which does not.

## The counterexample (α = 0, ε = 6)

* Module X on `Fin 3`: two `⊤`-born points `a₁ = 0, a₂ = 1` that merge with each other at
  time `100`, and a point `p = 2` born at `110` that merges into `a₁` at time `89`.
  Its rank (for `t ≤ s`): `rX s t = 1 + [t > 100] + [s ≤ 110 ∧ t > 89]`.
* Module Y on `Fin 2`: two `⊤`-born points merging at time `94`, nothing else.
  Its rank: `rY s t = 1 + [t > 94]` (independent of `s`).

Diagrams: `mult rX` is `δ_{(110, 89)}` (one finite bar); `mult rY ≡ 0` — Y's only event,
the merge of its `⊤`-born pair at time `94`, is the point `(⊤, 94)`, which the `mult`
guard kills. The truncated diagrams `mult (truncRank · 0)` are the same (`DX = {(110,89)}`,
`DY = ∅`): truncation at `α = 0` only clamps deaths to `α`, and neither diagram has
essential (`d = -∞`) or sub-`α` points.

`hbox` at `ε = 6` HOLDS: the two `⊤`-born structures are ε-interleaved (X's pair merges at
100, Y's at 94 ≤ 100 + 6... precisely `M_Y ≥ M_X - ε` and `M_X ≥ M_Y - ε`), and X's bar
`(110, 89)` only ever contributes to `rX s t` at windows with `89 < t ≤ 98` (because
`t + 2ε ≤ s ≤ 110` forces `t ≤ 98`), where `rY (s-ε) (t+ε)` already reads `2` from Y's
still-separate `⊤`-born pair (`t + 6 > 94`). Formally:
`rX s t ≤ 3` always, `rX s t = 3` needs `t > 100 ∧ s ≤ 110`, which contradicts
`t + 12 ≤ s`; the remaining values `≤ 2` are covered by the case analysis proved below.

But NO `δ` exists: the single off-diagonal X-copy at `(110, 89)` has prominence
`110 - 89 = 21 > 2ε = 12`, so it cannot be matched to any diagonal copy
(`x ∈ [104,116] ∩ [83,95] = ∅`), and `DY = ∅` has no off-diagonal copies at all.

## What a corrected statement needs

Add the paper's tameness/emptiness hypothesis, e.g.
`(∃ s₀ : ℝ, ∀ s ≥ s₀, stage s = ∅)`, to the child (it is satisfied by `superRank`
and `ripsRank` in Theorem 4.5's setting and kills `⊤`-born classes). Then the
rank function equals the box-count of the truncated diagram with NO correction term,
and the Extended Stability route (η-grid, Eqs. 19–22, Hall matching) applies.
-/

/-! ### Trivial helpers -/

theorem t45s_zero_le (a : ℕ∞) : (0 : ℕ∞) ≤ a := (zero_le : (0 : ℕ∞) ≤ a)

/-- `IsDiagramLike (mult r)` holds for EVERY rank function `r` (a point of positive
multiplicity must lie in a nonzero branch, which forces `p.2 < p.1`). -/
theorem t45s_isDiagramLike_mult (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  by_contra hne
  have hle : p.1 ≤ p.2 := not_lt.mp hne
  have h0 : mult r p = 0 := by
    unfold mult
    by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
    · rw [if_pos h1]
      by_cases h2 : p.2 = ⊥
      · have hle' : p.1 ≤ ⊥ := h2 ▸ hle
        exact absurd (le_antisymm hle' bot_le) h1.1
      · rw [if_neg h2]
        by_cases h3 : p.2 < p.1
        · exact absurd h3 (not_lt.mpr hle)
        · rw [if_neg h3]
    · rw [if_neg h1]
  exact hp h0

/-- Unfolds `mult r ((b:ℝ):EReal, (d:ℝ):EReal)` for `d < b`. -/
theorem t45s_mult_coe_coe (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (hbd : d < b) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) =
      ⨅ (η : ℝ) (_ : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2)),
        ((r (b - η) (d + η) - r (b + η) (d + η)) -
          (r (b - η) (d - η) - r (b + η) (d - η))) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (EReal.coe_ne_bot d), if_pos (EReal.coe_lt_coe_iff.mpr hbd)]
  simp only [EReal.toReal_coe]

/-- Unfolds `mult r ((b:ℝ):EReal, ⊥)`. -/
theorem t45s_mult_coe_bot (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊥ : EReal)) =
      ⨅ (η : ℝ) (_ : 0 < η), ⨅ (t : ℝ) (_ : t ≤ b - η),
        (r (b - η) t - r (b + η) t) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_pos rfl]
  simp only [EReal.toReal_coe]

/-! ### General facts about truncated diagrams -/

/-- `truncRank r α s t = 0` whenever the second window is below `α`. -/
theorem t45s_truncRank_zero_of_lt (r : ℝ → ℝ → ℕ∞) (α s t : ℝ) (ht : t < α) :
    truncRank r α s t = 0 := by
  show (if α ≤ s ∧ α ≤ t then r s t else 0) = 0
  exact if_neg (fun h => not_le.mpr ht h.2)

/-- `truncRank r α s t = r s t` whenever both windows are at or above `α` (Eq. 18). -/
theorem t45s_truncRank_eq (r : ℝ → ℝ → ℕ∞) (α s t : ℝ) (hs : α ≤ s) (ht : α ≤ t) :
    truncRank r α s t = r s t := by
  show (if α ≤ s ∧ α ≤ t then r s t else 0) = r s t
  exact if_pos (And.intro hs ht)

/-- The truncated diagram has NO essential `(b, ⊥)` points: the `(b, ⊥)` multiplicity
probes second arguments `t ≤ b - η`, and among them `t < α` makes the truncated rank `0`,
so the infimum is `0`. -/
theorem t45s_mult_trunc_bot_zero (r : ℝ → ℝ → ℕ∞) (α b : ℝ) :
    mult (truncRank r α) (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [t45s_mult_coe_bot]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    t45s_zero_le _)
  have ht0 : min (b - 1) (α - 1) < α := by
    have := min_le_right (b - 1) (α - 1)
    have h1 := min_le_left (b - 1) (α - 1)
    linarith
  have hval : truncRank r α (b - 1) (min (b - 1) (α - 1)) -
      truncRank r α (b + 1) (min (b - 1) (α - 1)) ≤ 0 := by
    rw [t45s_truncRank_zero_of_lt r α _ _ ht0, t45s_truncRank_zero_of_lt r α _ _ ht0,
      tsub_self]
  exact iInf_le_of_le 1 (iInf_le_of_le (show (0 : ℝ) < 1 by norm_num)
    (iInf_le_of_le (min (b - 1) (α - 1)) (iInf_le_of_le (min_le_left _ _) hval)))

/-- The truncated diagram vanishes strictly below `α`: for real `d < α`, a window probe
`η < α - d` sends all four truncated corner ranks to `0`. -/
theorem t45s_mult_trunc_lt_zero (r : ℝ → ℝ → ℕ∞) (α b d : ℝ) (hbd : d < b) (hd : d < α) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [t45s_mult_coe_coe _ b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => t45s_zero_le _)
  have hm1 : min ((b - d) / 2) (α - d) ≤ (b - d) / 2 := min_le_left _ _
  have hm2 : min ((b - d) / 2) (α - d) ≤ α - d := min_le_right _ _
  have hpos : (0 : ℝ) < min ((b - d) / 2) (α - d) := lt_min (by linarith) (by linarith)
  set η : ℝ := min ((b - d) / 2) (α - d) / 2 with hη
  have hηpos : (0 : ℝ) < η := by rw [hη]; linarith
  have hηmem : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := by
    constructor <;> rw [hη] <;> linarith
  have hdη : d + η < α := by rw [hη]; linarith
  have hval : (truncRank r α (b - η) (d + η) - truncRank r α (b + η) (d + η)) -
      (truncRank r α (b - η) (d - η) - truncRank r α (b + η) (d - η)) ≤ 0 := by
    rw [t45s_truncRank_zero_of_lt r α _ _ hdη,
        t45s_truncRank_zero_of_lt r α _ _ hdη,
        t45s_truncRank_zero_of_lt r α _ _ (by linarith : d - η < α),
        t45s_truncRank_zero_of_lt r α _ _ (by linarith : d - η < α)]
    simp
  exact iInf_le_of_le η (iInf_le_of_le hηmem hval)

/-! ## The counterexample modules

`X` on `Fin 3`: two `⊤`-born points `0, 1` (present in `cexStageX u` for every real `u`)
that merge with each other at time `100`, and a point `2` born at `110` merging into `0`
at time `89`. `Y` on `Fin 2`: two `⊤`-born points merging at time `94`, nothing else. -/

/-- The stage function of module X. -/
def cexStageX : ℝ → Set (Fin 3) := fun u => if u ≤ 110 then Set.univ else {0, 1}

/-- The component relation of module X. -/
def cexJX : ℝ → Fin 3 → Fin 3 → Prop := fun t x y =>
  x ∈ cexStageX t ∧ y ∈ cexStageX t ∧ (x = y ∨ (t ≤ 100 ∧ x ≤ 1 ∧ y ≤ 1) ∨ t ≤ 89)

/-- The stage function of module Y: never empty. -/
def cexStageY : ℝ → Set (Fin 2) := fun _ => Set.univ

/-- The component relation of module Y. -/
def cexJY : ℝ → Fin 2 → Fin 2 → Prop := fun t x y => x = y ∨ t ≤ 94

theorem cex_stageX_mem_iff (t : ℝ) (x : Fin 3) :
    x ∈ cexStageX t ↔ (x = 0 ∨ x = 1 ∨ t ≤ 110) := by
  unfold cexStageX
  by_cases ht : t ≤ 110
  · rw [if_pos ht]; simp [ht]
  · rw [if_neg ht]; simp [ht]

theorem cex_stageX_antitone {s t : ℝ} (hst : s ≤ t) : cexStageX t ⊆ cexStageX s := by
  intro x hx
  rw [cex_stageX_mem_iff] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (le_trans hst h))

/-- `X` is a genuine filtration module. -/
theorem cex_hLawX : FiltrationLaw cexStageX cexJX := by
  refine ⟨fun s t hst => cex_stageX_antitone hst, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x y h; exact ⟨h.1, h.2.1⟩
  · intro t x hx; exact ⟨hx, hx, Or.inl rfl⟩
  · intro t x y h
    refine ⟨h.2.1, h.1, ?_⟩
    rcases h.2.2 with h1 | h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inl ⟨h1.1, h1.2.2, h1.2.1⟩)
    · exact Or.inr (Or.inr h1)
  · intro t x y z hxy hyz
    refine ⟨hxy.1, hyz.2.1, ?_⟩
    rcases hxy.2.2 with h1 | h1 | h1
    · rcases hyz.2.2 with h2 | h2 | h2
      · exact Or.inl (h1.trans h2)
      · exact Or.inr (Or.inl ⟨h2.1, h1 ▸ h2.2.1, h2.2.2⟩)
      · exact Or.inr (Or.inr h2)
    · rcases hyz.2.2 with h2 | h2 | h2
      · exact Or.inr (Or.inl ⟨h1.1, h1.2.1, h2 ▸ h1.2.2⟩)
      · exact Or.inr (Or.inl ⟨h1.1, h1.2.1, h2.2.2⟩)
      · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inr h1)
  · intro s t hst x y h
    refine ⟨cex_stageX_antitone hst h.1, cex_stageX_antitone hst h.2.1, ?_⟩
    rcases h.2.2 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨by linarith, h1.2.1, h1.2.2⟩)
    · exact Or.inr (Or.inr (by linarith))

/-- `Y` is a genuine filtration module. -/
theorem cex_hLawY : FiltrationLaw cexStageY cexJY := by
  refine ⟨fun s t _ => (fun x hx => hx : cexStageY t ⊆ cexStageY s), ?_, ?_, ?_, ?_, ?_⟩
  · intro t x y h; exact ⟨Set.mem_univ x, Set.mem_univ y⟩
  · intro t x _; exact Or.inl rfl
  · intro t x y h
    rcases h with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1
  · intro t x y z hxy hyz
    rcases hxy with h1 | h1
    · rcases hyz with h2 | h2
      · exact Or.inl (h1.trans h2)
      · exact Or.inr h2
    · rcases hyz with h2 | h2
      · exact Or.inr h1
      · exact Or.inr h1
  · intro s t hst x y h
    rcases h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hst.trans h1)

/-! ### Rank functions of the two modules

`rankFn` computes the encard of the image of `x ↦ {y | J t x y}` over `stage s`.
We unfold it for both modules. -/

/-- On `Fin 3`, a point that is not `≤ 1` is `2`. -/
theorem cex_fin3_eq_two (x : Fin 3) (h : ¬ x ≤ 1) : x = 2 := by
  fin_cases x <;> simp_all

theorem cex_stageX_univ (t : ℝ) (ht : t ≤ 110) : cexStageX t = (Set.univ : Set (Fin 3)) := by
  unfold cexStageX; rw [if_pos ht]

theorem cex_stageX_pair (t : ℝ) (ht : 110 < t) : cexStageX t = ({0, 1} : Set (Fin 3)) := by
  unfold cexStageX; rw [if_neg (not_le.mpr ht)]

theorem cex_mem_stageX (t : ℝ) (ht : t ≤ 110) (x : Fin 3) : x ∈ cexStageX t :=
  (cex_stageX_mem_iff t x).2 (Or.inr (Or.inr ht))

/-- Points `0` and `1` of `Fin 3` are present at every time. -/
theorem cex_mem_stageX_0 (t : ℝ) : (0 : Fin 3) ∈ cexStageX t :=
  (cex_stageX_mem_iff t 0).2 (Or.inl rfl)

theorem cex_mem_stageX_1 (t : ℝ) : (1 : Fin 3) ∈ cexStageX t :=
  (cex_stageX_mem_iff t 1).2 (Or.inr (Or.inl rfl))

/-- Class of a point present in `stage t`, when `t ≤ 89`: everything present is one class. -/
theorem cex_classX_le89 (t : ℝ) (ht : t ≤ 89) (x : Fin 3) (hx : x ∈ cexStageX t) :
    {y : Fin 3 | cexJX t x y} = cexStageX t := by
  ext y
  simp only [Set.mem_ofPred_eq]
  show
    (x ∈ cexStageX t ∧ y ∈ cexStageX t ∧ (x = y ∨ (t ≤ 100 ∧ x ≤ 1 ∧ y ≤ 1) ∨ t ≤ 89)) ↔
    y ∈ cexStageX t
  constructor
  · intro h; exact h.2.1
  · intro hy; exact ⟨hx, hy, Or.inr (Or.inr ht)⟩

/-- Class of a point present in `stage t`, when `89 < t ≤ 100`: points `≤ 1` form the class
`{y | y ≤ 1}`, point `2` is alone. -/
theorem cex_classX_mid (t : ℝ) (h1 : 89 < t) (h2 : t ≤ 100) (x : Fin 3)
    (hx : x ∈ cexStageX t) :
    {y : Fin 3 | cexJX t x y} =
      if x ≤ 1 then {y : Fin 3 | y ≤ 1} else ({x} : Set (Fin 3)) := by
  have ht110 : t ≤ 110 := by linarith
  by_cases hx1 : x ≤ 1
  · rw [if_pos hx1]
    ext y
    simp only [Set.mem_ofPred_eq]
    show
      (x ∈ cexStageX t ∧ y ∈ cexStageX t ∧ (x = y ∨ (t ≤ 100 ∧ x ≤ 1 ∧ y ≤ 1) ∨ t ≤ 89)) ↔
      y ≤ 1
    constructor
    · rintro ⟨-, -, h⟩
      rcases h with hxy | ⟨-, hx1', hy1⟩ | h89
      · exact hxy ▸ hx1
      · exact hy1
      · exact (not_le.mpr h1 h89).elim
    · intro hy1
      exact ⟨hx, cex_mem_stageX t ht110 y, Or.inr (Or.inl ⟨h2, hx1, hy1⟩)⟩
  · rw [if_neg hx1]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    show
      (x ∈ cexStageX t ∧ y ∈ cexStageX t ∧ (x = y ∨ (t ≤ 100 ∧ x ≤ 1 ∧ y ≤ 1) ∨ t ≤ 89)) ↔
      y = x
    constructor
    · rintro ⟨-, -, h⟩
      rcases h with hxy | ⟨-, hx1', -⟩ | h89
      · exact hxy.symm
      · exact (hx1 hx1').elim
      · exact (not_le.mpr h1 h89).elim
    · rintro hy   -- hy : y = x
      have hys : y ∈ cexStageX t := by rw [hy]; exact hx
      exact ⟨hx, hys, Or.inl hy.symm⟩

/-- Class of a point present in `stage t`, when `100 < t`: singleton classes. -/
theorem cex_classX_gt100 (t : ℝ) (ht : 100 < t) (x : Fin 3) (hx : x ∈ cexStageX t) :
    {y : Fin 3 | cexJX t x y} = ({x} : Set (Fin 3)) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  show
    (x ∈ cexStageX t ∧ y ∈ cexStageX t ∧ (x = y ∨ (t ≤ 100 ∧ x ≤ 1 ∧ y ≤ 1) ∨ t ≤ 89)) ↔
    y = x
  constructor
  · rintro ⟨-, -, h⟩
    rcases h with hxy | ⟨h100, -, -⟩ | h89
    · exact hxy.symm
    · exact (not_le.mpr ht h100).elim
    · exact (not_le.mpr (by linarith) h89).elim
  · rintro hy   -- hy : y = x
    have hys : y ∈ cexStageX t := by rw [hy]; exact hx
    exact ⟨hx, hys, Or.inl hy.symm⟩

/-- `rX s t = 1` when `t ≤ 89`. -/
theorem cex_rankX_le89 (s t : ℝ) (ht : t ≤ 89) :
    rankFn cexStageX cexJX s t = 1 := by
  show ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s).encard = 1
  have ht110 : t ≤ 110 := by linarith
  have himg : ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s)
      = ({cexStageX t} : Set (Set (Fin 3))) := by
    ext C
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact cex_classX_le89 t ht x (cex_mem_stageX t ht110 x)
    · rintro rfl
      refine ⟨(0 : Fin 3), (cex_stageX_mem_iff s 0).2 (Or.inl rfl), ?_⟩
      exact cex_classX_le89 t ht 0 (cex_mem_stageX t ht110 0)
  rw [himg, Set.encard_singleton]

/-- `rX s t = 2` when `89 < t ≤ 100` and `s ≤ 110`. -/
theorem cex_rankX_mid_le (s t : ℝ) (h1 : 89 < t) (h2 : t ≤ 100) (hs : s ≤ 110) :
    rankFn cexStageX cexJX s t = 2 := by
  show ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s).encard = 2
  have ht110 : t ≤ 110 := by linarith
  rw [cex_stageX_univ s hs]
  have hne : ({y : Fin 3 | y ≤ 1} : Set (Fin 3)) ≠ ({(2 : Fin 3)} : Set (Fin 3)) := by
    intro h
    have h2 : (2 : Fin 3) ∈ {y : Fin 3 | y ≤ 1} := by
      rw [h]; exact Set.mem_singleton _
    exact absurd h2 (by simp)
  have himg :
      ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' (Set.univ : Set (Fin 3))) =
        ({({y : Fin 3 | y ≤ 1}), ({(2 : Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) := by
    ext C
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx1 : x ≤ 1
      · exact Or.inl (by rw [cex_classX_mid t h1 h2 x (cex_mem_stageX t ht110 x), if_pos hx1])
      · refine Or.inr ?_
        have hx2 : x = 2 := cex_fin3_eq_two x hx1
        subst hx2
        rw [cex_classX_mid t h1 h2 2 (cex_mem_stageX t ht110 2),
            if_neg (by decide : ¬ ((2 : Fin 3) ≤ 1))]
    · rintro (rfl | rfl)
      · exact ⟨(0 : Fin 3),
          by rw [cex_classX_mid t h1 h2 0 (cex_mem_stageX t ht110 0),
                 if_pos (by decide : (0 : Fin 3) ≤ 1)]⟩
      · exact ⟨(2 : Fin 3),
          by rw [cex_classX_mid t h1 h2 2 (cex_mem_stageX t ht110 2),
                 if_neg (by decide : ¬ ((2 : Fin 3) ≤ 1))]⟩
  rw [himg, Set.encard_pair hne]

/-- `rX s t = 1` when `89 < t ≤ 100` and `110 < s`. -/
theorem cex_rankX_mid_gt (s t : ℝ) (h1 : 89 < t) (h2 : t ≤ 100) (hs : 110 < s) :
    rankFn cexStageX cexJX s t = 1 := by
  show ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s).encard = 1
  have ht110 : t ≤ 110 := by linarith
  have himg : ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s)
      = ({({y : Fin 3 | y ≤ 1})} : Set (Set (Fin 3))) := by
    ext C
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : x ≤ 1 := by
        rcases (cex_stageX_mem_iff s x).1 hx with rfl | rfl | hs110
        · decide
        · decide
        · exact absurd hs110 (not_le.mpr hs)
      rw [cex_classX_mid t h1 h2 x (cex_mem_stageX t ht110 x), if_pos hx1]
    · rintro rfl
      exact ⟨(0 : Fin 3), (cex_stageX_mem_iff s 0).2 (Or.inl rfl),
        by rw [cex_classX_mid t h1 h2 0 (cex_mem_stageX t ht110 0),
               if_pos (by decide : (0 : Fin 3) ≤ 1)]⟩
  rw [himg, Set.encard_singleton]

/-- `rX s t = 3` when `100 < t ≤ s ≤ 110`. -/
theorem cex_rankX_gt100_le (s t : ℝ) (ht : 100 < t) (hst : t ≤ s) (hs : s ≤ 110) :
    rankFn cexStageX cexJX s t = 3 := by
  show ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s).encard = 3
  have ht110 : t ≤ 110 := by linarith
  rw [cex_stageX_univ s hs]
  have hfun : (fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) =
      fun x => ({x} : Set (Fin 3)) := by
    funext x
    exact cex_classX_gt100 t ht x (cex_mem_stageX t ht110 x)
  rw [hfun, Set.singleton_injective.encard_image, Set.encard_univ]
  have h3 : ENat.card (Fin 3) = 3 := by
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]; norm_num
  rw [h3]

/-- `rX s t = 2` when `100 < t` and `110 < s` (so `t ≤ s` is automatic for the
probes/hbox we use; here only `110 < s` is needed). -/
theorem cex_rankX_gt100_gt (s t : ℝ) (ht : 100 < t) (hs : 110 < s) :
    rankFn cexStageX cexJX s t = 2 := by
  show ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s).encard = 2
  have hne : ({(0 : Fin 3)} : Set (Fin 3)) ≠ ({(1 : Fin 3)} : Set (Fin 3)) := by
    intro h
    have h0 : (0 : Fin 3) ∈ ({1} : Set (Fin 3)) := h ▸ Set.mem_singleton 0
    exact absurd h0 (by simp)
  have himg : ((fun x : Fin 3 => {y : Fin 3 | cexJX t x y}) '' cexStageX s)
      = ({({(0 : Fin 3)} : Set (Fin 3)), ({(1 : Fin 3)} : Set (Fin 3))} :
          Set (Set (Fin 3))) := by
    ext C
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (cex_stageX_mem_iff s x).1 hx with rfl | rfl | hs110
      · exact Or.inl (cex_classX_gt100 t ht 0 (cex_mem_stageX_0 t))
      · exact Or.inr (cex_classX_gt100 t ht 1 (cex_mem_stageX_1 t))
      · exact absurd hs110 (not_le.mpr hs)
    · rintro (rfl | rfl)
      · exact ⟨(0 : Fin 3), (cex_stageX_mem_iff s 0).2 (Or.inl rfl),
          by rw [cex_classX_gt100 t ht 0 (cex_mem_stageX_0 t)]⟩
      · exact ⟨(1 : Fin 3), (cex_stageX_mem_iff s 1).2 (Or.inr (Or.inl rfl)),
          by rw [cex_classX_gt100 t ht 1 (cex_mem_stageX_1 t)]⟩
  rw [himg, Set.encard_pair hne]

/-- Class of a point in module `Y`: one class (`univ`) when `t ≤ 94`, a singleton when `t > 94`. -/
theorem cex_classY (t : ℝ) (x : Fin 2) :
    {y : Fin 2 | cexJY t x y} =
      if t ≤ 94 then (Set.univ : Set (Fin 2)) else ({x} : Set (Fin 2)) := by
  by_cases ht : t ≤ 94
  · rw [if_pos ht]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ]
    show (x = y ∨ t ≤ 94) ↔ True
    simp [ht]
  · rw [if_neg ht]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    show (x = y ∨ t ≤ 94) ↔ y = x
    constructor
    · rintro (hxy | h)
      · exact hxy.symm
      · exact absurd h ht
    · intro hy; exact Or.inl hy.symm

/-- `rY s t = 1` when `t ≤ 94`, `2` when `94 < t` (independent of `s`). -/
theorem cex_rankY_le (s t : ℝ) (ht : t ≤ 94) :
    rankFn cexStageY cexJY s t = 1 := by
  show ((fun x : Fin 2 => {y : Fin 2 | cexJY t x y}) '' cexStageY s).encard = 1
  have hs : cexStageY s = (Set.univ : Set (Fin 2)) := rfl
  rw [hs]
  have himg : ((fun x : Fin 2 => {y : Fin 2 | cexJY t x y}) '' (Set.univ : Set (Fin 2)))
      = ({(Set.univ : Set (Fin 2))} : Set (Set (Fin 2))) := by
    ext C
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      rw [cex_classY t x, if_pos ht]
    · rintro rfl
      exact ⟨(0 : Fin 2), by rw [cex_classY t 0, if_pos ht]⟩
  rw [himg, Set.encard_singleton]

/-- `rY s t = 2` when `94 < t`. -/
theorem cex_rankY_gt (s t : ℝ) (ht : 94 < t) :
    rankFn cexStageY cexJY s t = 2 := by
  show ((fun x : Fin 2 => {y : Fin 2 | cexJY t x y}) '' cexStageY s).encard = 2
  have hs : cexStageY s = (Set.univ : Set (Fin 2)) := rfl
  have hne : ¬ (t ≤ 94) := not_le.mpr ht
  rw [hs]
  have hfun : (fun x : Fin 2 => {y : Fin 2 | cexJY t x y}) =
      fun x => ({x} : Set (Fin 2)) := funext fun x => by rw [cex_classY t x, if_neg hne]
  rw [hfun, Set.singleton_injective.encard_image, Set.encard_univ]
  have h2 : ENat.card (Fin 2) = 2 := by
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]; norm_num
  rw [h2]


/-! ### Window differences of the rank functions

The `mult` probes are second differences of `r` over an `s`-window. Everything below reduces
to the single structural fact: an `s`-window difference of `rX` is `1` exactly when the
window straddles the birth time `110` (first side `≤ 110`, second side `> 110`) and the death
coordinate is above the merge time `89`. -/

/-- `truncRank r α s t = 0` whenever the FIRST window is below `α`. -/
theorem t45s_truncRank_zero_of_lt' (r : ℝ → ℝ → ℕ∞) (α s t : ℝ) (hs : s < α) :
    truncRank r α s t = 0 := by
  show (if α ≤ s ∧ α ≤ t then r s t else 0) = 0
  exact if_neg (fun h => absurd h.1 (not_le.mpr hs))

/-- `mult r` vanishes at real `b` with second coordinate `⊤` (the `p.2 < p.1` branch is
unreachable when `p.2 = ⊤`). -/
theorem t45s_mult_coe_top (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊤ : EReal)) = 0 := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (Ne.symm (bot_ne_top : (⊥ : EReal) ≠ ⊤)),
      if_neg (fun h => EReal.coe_ne_top b (le_antisymm le_top h.le))]

/-- `rY` does not depend on its first argument. -/
theorem cex_rankY_indep (s₁ s₂ t : ℝ) :
    rankFn cexStageY cexJY s₁ t = rankFn cexStageY cexJY s₂ t := by
  rcases le_or_gt t 94 with h94 | h94
  · rw [cex_rankY_le s₁ t h94, cex_rankY_le s₂ t h94]
  · rw [cex_rankY_gt s₁ t h94, cex_rankY_gt s₂ t h94]

/-- The `s`-window difference of `rX` (untruncated), for `t ≤ s₁ ≤ s₂`. -/
theorem cex_diffX (s₁ s₂ t : ℝ) (h : s₁ ≤ s₂) (ht : t ≤ s₁) :
    rankFn cexStageX cexJX s₁ t - rankFn cexStageX cexJX s₂ t =
      if s₁ ≤ 110 ∧ 110 < s₂ ∧ 89 < t then 1 else 0 := by
  by_cases hA : s₁ ≤ 110 ∧ 110 < s₂
  · by_cases ht89 : 89 < t
    · rcases le_or_gt t 100 with h100 | h100
      · rw [cex_rankX_mid_le s₁ t ht89 h100 hA.1, cex_rankX_mid_gt s₂ t ht89 h100 hA.2,
            if_pos ⟨hA.1, hA.2, ht89⟩]
        decide
      · rw [cex_rankX_gt100_le s₁ t h100 ht hA.1, cex_rankX_gt100_gt s₂ t h100 hA.2,
            if_pos ⟨hA.1, hA.2, ht89⟩]
        decide
    · have ht' : t ≤ 89 := le_of_not_gt ht89
      rw [cex_rankX_le89 s₁ t ht', cex_rankX_le89 s₂ t ht',
          if_neg (fun hc => ht89 hc.2.2)]
      decide
  · rcases not_and_or.mp hA with hs1 | hs2
    · have hs1' : 110 < s₁ := not_le.mp hs1
      have hs2' : 110 < s₂ := lt_of_lt_of_le hs1' h
      rcases le_or_gt t 89 with ht89 | ht89
      · rw [cex_rankX_le89 s₁ t ht89, cex_rankX_le89 s₂ t ht89, if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩)]
        decide
      · rcases le_or_gt t 100 with h100 | h100
        · rw [cex_rankX_mid_gt s₁ t ht89 h100 hs1', cex_rankX_mid_gt s₂ t ht89 h100 hs2',
              if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩)]
          decide
        · rw [cex_rankX_gt100_gt s₁ t h100 hs1', cex_rankX_gt100_gt s₂ t h100 hs2',
              if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩)]
          decide
    · have hs2' : s₂ ≤ 110 := le_of_not_gt hs2
      have hs1' : s₁ ≤ 110 := le_trans h hs2'
      rcases le_or_gt t 89 with ht89 | ht89
      · rw [cex_rankX_le89 s₁ t ht89, cex_rankX_le89 s₂ t ht89, if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩)]
        decide
      · rcases le_or_gt t 100 with h100 | h100
        · rw [cex_rankX_mid_le s₁ t ht89 h100 hs1', cex_rankX_mid_le s₂ t ht89 h100 hs2',
              if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩)]
          decide
        · rw [cex_rankX_gt100_le s₁ t h100 ht hs1',
              cex_rankX_gt100_le s₂ t h100 (le_trans ht h) hs2', if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩)]
          decide

/-- The `s`-window difference of the TRUNCATED rank of `X` (at `α = 0`), for `t ≤ s₁ ≤ s₂`. -/
theorem cex_diffXt (s₁ s₂ t : ℝ) (h : s₁ ≤ s₂) (ht : t ≤ s₁) :
    truncRank (rankFn cexStageX cexJX) 0 s₁ t - truncRank (rankFn cexStageX cexJX) 0 s₂ t =
      if 0 ≤ s₁ ∧ s₁ ≤ 110 ∧ 110 < s₂ ∧ 0 ≤ t ∧ 89 < t then 1 else 0 := by
  by_cases h0 : 0 ≤ s₁
  · by_cases htn : t < 0
    · rw [t45s_truncRank_zero_of_lt (rankFn cexStageX cexJX) 0 s₁ t htn,
          t45s_truncRank_zero_of_lt (rankFn cexStageX cexJX) 0 s₂ t htn,
          if_neg (fun hc => absurd hc.2.2.2.1 (not_le.mpr htn))]
      decide
    · have h0t : 0 ≤ t := le_of_not_gt htn
      rw [t45s_truncRank_eq (rankFn cexStageX cexJX) 0 s₁ t h0 h0t,
          t45s_truncRank_eq (rankFn cexStageX cexJX) 0 s₂ t (h0.trans h) h0t,
          cex_diffX s₁ s₂ t h ht]
      by_cases hA : s₁ ≤ 110 ∧ 110 < s₂
      · by_cases ht89 : 89 < t
        · rw [if_pos ⟨hA.1, hA.2, ht89⟩, if_pos ⟨h0, hA.1, hA.2, h0t, ht89⟩]
        · rw [if_neg (fun hc => ht89 hc.2.2), if_neg (fun hc => ht89 hc.2.2.2.2)]
      · rw [if_neg (fun hc => hA ⟨hc.1, hc.2.1⟩),
            if_neg (fun hc => hA ⟨hc.2.1, hc.2.2.1⟩)]
  · rw [t45s_truncRank_zero_of_lt' (rankFn cexStageX cexJX) 0 s₁ t (not_le.mp h0), zero_tsub,
       if_neg (fun hc => h0 hc.1)]

/-- The `s`-window difference of the TRUNCATED rank of `Y` is always `0`: `rY` is
independent of `s`, and the truncation guard `0 ≤ s` is monotone in `s`. -/
theorem cex_diffYt (s₁ s₂ t : ℝ) (h : s₁ ≤ s₂) :
    truncRank (rankFn cexStageY cexJY) 0 s₁ t - truncRank (rankFn cexStageY cexJY) 0 s₂ t = 0 := by
  by_cases h0 : 0 ≤ s₁
  · by_cases htn : t < 0
    · rw [t45s_truncRank_zero_of_lt (rankFn cexStageY cexJY) 0 s₁ t htn,
          t45s_truncRank_zero_of_lt (rankFn cexStageY cexJY) 0 s₂ t htn, tsub_self]
    · have h0t : 0 ≤ t := le_of_not_gt htn
      rw [t45s_truncRank_eq (rankFn cexStageY cexJY) 0 s₁ t h0 h0t,
          t45s_truncRank_eq (rankFn cexStageY cexJY) 0 s₂ t (h0.trans h) h0t,
          cex_rankY_indep s₁ s₂ t, tsub_self]
  · rw [t45s_truncRank_zero_of_lt' (rankFn cexStageY cexJY) 0 s₁ t (not_le.mp h0), zero_tsub]

/-! ### Multiplicities of the two (truncated) diagrams

`mult (truncRank rY 0) ≡ 0` (Y's `s`-window differences all vanish), and the only nonzero
point of `mult (truncRank rX 0)` that we need is `((110, 89))` with value `1`
(plus the untruncated analogues for the hypotheses). -/

/-- Untruncated `s`-window difference of `rY` is always `0` (rank independent of `s`). -/
theorem cex_diffY (s₁ s₂ t : ℝ) :
    rankFn cexStageY cexJY s₁ t - rankFn cexStageY cexJY s₂ t = 0 := by
  have h := cex_rankY_indep s₁ s₂ t
  rw [h, tsub_self]

/-- `mult rY ((b:ℝ), (d:ℝ)) = 0` for real `d < b`. -/
theorem cex_multY_coe_coe (b d : ℝ) (hbd : d < b) :
    mult (rankFn cexStageY cexJY) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [t45s_mult_coe_coe _ b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => t45s_zero_le _)
  have hmem : ((b - d) / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) :=
    ⟨by linarith, by linarith⟩
  refine iInf_le_of_le ((b - d) / 4) (iInf_le_of_le hmem ?_)
  have e1 := cex_diffY (b - (b - d) / 4) (b + (b - d) / 4) (d + (b - d) / 4)
  have e2 := cex_diffY (b - (b - d) / 4) (b + (b - d) / 4) (d - (b - d) / 4)
  rw [e1, e2, tsub_self]

/-- `mult rY ((b:ℝ), ⊥) = 0`. -/
theorem cex_multY_coe_bot (b : ℝ) :
    mult (rankFn cexStageY cexJY) (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [t45s_mult_coe_bot]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    t45s_zero_le _)
  refine iInf_le_of_le 1 (iInf_le_of_le (show (0 : ℝ) < 1 by norm_num)
    (iInf_le_of_le (b - 1) (iInf_le_of_le le_rfl ?_)))
  rw [cex_diffY (b - 1) (b + 1) (b - 1)]

/-- `mult rY ≡ 0` (the untruncated diagram of Y is empty). -/
theorem cex_multY_zero (p : EReal × EReal) : mult (rankFn cexStageY cexJY) p = 0 := by
  obtain ⟨b, d⟩ := p
  by_cases hb1 : b = ⊥
  · subst hb1; simp [mult]
  by_cases hb2 : b = ⊤
  · subst hb2; simp [mult]
  obtain ⟨br, rfl⟩ : ∃ br : ℝ, b = ((br : ℝ) : EReal) :=
    ⟨b.toReal, (EReal.coe_toReal hb2 hb1).symm⟩
  by_cases hd1 : d = ⊥
  · subst hd1; exact cex_multY_coe_bot br
  by_cases hd2 : d = ⊤
  · subst hd2; exact t45s_mult_coe_top _ br
  obtain ⟨dr, rfl⟩ : ∃ dr : ℝ, d = ((dr : ℝ) : EReal) :=
    ⟨d.toReal, (EReal.coe_toReal hd2 hd1).symm⟩
  by_cases hdb : dr < br
  · exact cex_multY_coe_coe br dr hdb
  · unfold mult
    simp [EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_lt_coe_iff, hdb]

/-- `mult (truncRank rY 0) ((b:ℝ), (d:ℝ)) = 0` for real `d < b`. -/
theorem cex_multYt_coe_coe (b d : ℝ) (hbd : d < b) :
    mult (truncRank (rankFn cexStageY cexJY) 0)
      (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [t45s_mult_coe_coe _ b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => t45s_zero_le _)
  have hmem : ((b - d) / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) :=
    ⟨by linarith, by linarith⟩
  refine iInf_le_of_le ((b - d) / 4) (iInf_le_of_le hmem ?_)
  have e1 := cex_diffYt (b - (b - d) / 4) (b + (b - d) / 4) (d + (b - d) / 4) (by linarith)
  have e2 := cex_diffYt (b - (b - d) / 4) (b + (b - d) / 4) (d - (b - d) / 4) (by linarith)
  rw [e1, e2, tsub_self]

/-- `mult (truncRank rY 0) ≡ 0` (the truncated diagram of Y is empty). -/
theorem cex_multYt_zero (p : EReal × EReal) :
    mult (truncRank (rankFn cexStageY cexJY) 0) p = 0 := by
  obtain ⟨b, d⟩ := p
  by_cases hb1 : b = ⊥
  · subst hb1; simp [mult]
  by_cases hb2 : b = ⊤
  · subst hb2; simp [mult]
  obtain ⟨br, rfl⟩ : ∃ br : ℝ, b = ((br : ℝ) : EReal) :=
    ⟨b.toReal, (EReal.coe_toReal hb2 hb1).symm⟩
  by_cases hd1 : d = ⊥
  · subst hd1; exact t45s_mult_trunc_bot_zero _ 0 br
  by_cases hd2 : d = ⊤
  · subst hd2; exact t45s_mult_coe_top _ br
  obtain ⟨dr, rfl⟩ : ∃ dr : ℝ, d = ((dr : ℝ) : EReal) :=
    ⟨d.toReal, (EReal.coe_toReal hd2 hd1).symm⟩
  by_cases hdb : dr < br
  · exact cex_multYt_coe_coe br dr hdb
  · unfold mult
    simp [EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_lt_coe_iff, hdb]

/-- `mult rX ((110, 89)) = 1` (the single finite bar of X). -/
theorem cex_multX_coe_coe_110_89 :
    mult (rankFn cexStageX cexJX) (((110 : ℝ) : EReal), ((89 : ℝ) : EReal)) = 1 := by
  rw [t45s_mult_coe_coe _ 110 89 (by norm_num : (89 : ℝ) < 110)]
  refine le_antisymm ?_ ?_
  · -- ⨅ ≤ 1: witness η = 5
    have hmem : (5 : ℝ) ∈ Set.Ioo (0 : ℝ) ((110 - 89) / 2) := ⟨by norm_num, by norm_num⟩
    refine iInf_le_of_le 5 (iInf_le_of_le hmem ?_)
    rw [cex_rankX_mid_le (110 - 5) (89 + 5) (by norm_num) (by norm_num)
          (by norm_num : (110 : ℝ) - 5 ≤ 110),
        cex_rankX_mid_gt (110 + 5) (89 + 5) (by norm_num) (by norm_num)
          (by norm_num : (110 : ℝ) < 110 + 5),
        cex_rankX_le89 (110 - 5) (89 - 5) (by norm_num),
        cex_rankX_le89 (110 + 5) (89 - 5) (by norm_num)]
    decide
  · -- 1 ≤ ⨅: every η ∈ (0, 21/2) gives value 1
    refine le_iInf fun η => le_iInf fun hη => ?_
    rcases hη with ⟨h0, hlt⟩
    have h1 : 89 < 89 + η := by linarith
    have h2 : 89 + η ≤ 100 := by linarith
    have hs1 : 110 - η ≤ 110 := by linarith
    have hs2 : 110 < 110 + η := by linarith
    have ht2 : 89 - η ≤ 89 := by linarith
    rw [cex_rankX_mid_le (110 - η) (89 + η) h1 h2 hs1,
        cex_rankX_mid_gt (110 + η) (89 + η) h1 h2 hs2,
        cex_rankX_le89 (110 - η) (89 - η) ht2,
        cex_rankX_le89 (110 + η) (89 - η) ht2]
    decide

/-- `mult (truncRank rX 0) ((110, 89)) = 1` (truncation does not touch this bar: every probe
coordinate lies above `α = 0`). -/
theorem cex_multXt_coe_coe_110_89 :
    mult (truncRank (rankFn cexStageX cexJX) 0)
      (((110 : ℝ) : EReal), ((89 : ℝ) : EReal)) = 1 := by
  rw [t45s_mult_coe_coe _ 110 89 (by norm_num : (89 : ℝ) < 110)]
  refine le_antisymm ?_ ?_
  · have hmem : (5 : ℝ) ∈ Set.Ioo (0 : ℝ) ((110 - 89) / 2) := ⟨by norm_num, by norm_num⟩
    refine iInf_le_of_le 5 (iInf_le_of_le hmem ?_)
    have hs1 : (0 : ℝ) ≤ 110 - 5 := by norm_num
    have hs2 : (0 : ℝ) ≤ 110 + 5 := by norm_num
    have ht1 : (0 : ℝ) ≤ 89 + 5 := by norm_num
    have ht2 : (0 : ℝ) ≤ 89 - 5 := by norm_num
    rw [t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 - 5) (89 + 5) hs1 ht1,
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 + 5) (89 + 5) hs2 ht1,
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 - 5) (89 - 5) hs1 ht2,
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 + 5) (89 - 5) hs2 ht2,
        cex_rankX_mid_le (110 - 5) (89 + 5) (by norm_num) (by norm_num)
          (by norm_num : (110 : ℝ) - 5 ≤ 110),
        cex_rankX_mid_gt (110 + 5) (89 + 5) (by norm_num) (by norm_num)
          (by norm_num : (110 : ℝ) < 110 + 5),
        cex_rankX_le89 (110 - 5) (89 - 5) (by norm_num),
        cex_rankX_le89 (110 + 5) (89 - 5) (by norm_num)]
    decide
  · refine le_iInf fun η => le_iInf fun hη => ?_
    rcases hη with ⟨h0, hlt⟩
    have h1 : 89 < 89 + η := by linarith
    have h2 : 89 + η ≤ 100 := by linarith
    have hs1 : 110 - η ≤ 110 := by linarith
    have hs2 : 110 < 110 + η := by linarith
    have ht2 : 89 - η ≤ 89 := by linarith
    have hs1' : (0 : ℝ) ≤ 110 - η := by linarith
    have hs2' : (0 : ℝ) ≤ 110 + η := by linarith
    have ht1' : (0 : ℝ) ≤ 89 + η := by linarith
    have ht2' : (0 : ℝ) ≤ 89 - η := by linarith
    rw [t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 - η) (89 + η) hs1' ht1',
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 + η) (89 + η) hs2' ht1',
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 - η) (89 - η) hs1' ht2',
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (110 + η) (89 - η) hs2' ht2',
        cex_rankX_mid_le (110 - η) (89 + η) h1 h2 hs1,
        cex_rankX_mid_gt (110 + η) (89 + η) h1 h2 hs2,
        cex_rankX_le89 (110 - η) (89 - η) ht2,
        cex_rankX_le89 (110 + η) (89 - η) ht2]
    decide

/-! ### The conclusion fails: no `δ` moves the lone X-copy `(110, 89)` to `Y`'s empty diagram

`mult (truncRank rY 0) ≡ 0`, so `Y`'s truncated diagram has NO off-diagonal copies. The single
off-diagonal X-copy at `(110, 89)` (prominence `21 > 2ε = 12`) cannot land on a diagonal copy
of `Y` (`x ∈ [104, 116] ∩ [83, 95] = ∅`). Hence the matching the lemma asserts cannot exist. -/

/-- The conclusion of `theorem_4_5_lemma_4_6_corrected_stability` (at `α = 0`, `ε = 6`, modules
`X` and `Y`) is FALSE. -/
theorem cex_no_matching :
    ¬ ∃ δ : Copies (mult (truncRank (rankFn cexStageX cexJX) 0)) ≃
            Copies (mult (truncRank (rankFn cexStageY cexJY) 0)),
      (∀ a, closeE (pt a).1 (pt (δ a)).1 6 ∧ closeE (pt a).2 (pt (δ a)).2 6) ∧
      (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 6 ∧ closeE (pt (δ.symm b)).2 (pt b).2 6) := by
  rintro ⟨δ, h1, -⟩
  -- the off-diagonal X-copy at (110, 89)
  let a₀ : Copies (mult (truncRank (rankFn cexStageX cexJX) 0)) :=
    Sum.inl ⟨((((110 : ℝ) : EReal), ((89 : ℝ) : EReal)), (0 : ℕ)),
      (by
        show ((0 : ℕ) : ℕ∞) < mult (truncRank (rankFn cexStageX cexJX) 0)
            (((110 : ℝ) : EReal), ((89 : ℝ) : EReal))
        rw [cex_multXt_coe_coe_110_89]
        decide)⟩
  have hc := h1 a₀
  cases hd : δ a₀ with
  | inl q =>
    rw [hd] at hc
    have hq : ((q.1.2 : ℕ) : ℕ∞) <
        mult (truncRank (rankFn cexStageY cexJY) 0) q.1.1 := q.2
    rw [cex_multYt_zero q.1.1] at hq
    exact absurd hq (not_lt.mpr (t45s_zero_le _))
  | inr xk =>
    rw [hd] at hc
    have e1 : ((110 : ℝ) : EReal) ≤ xk.1 + ((6 : ℝ) : EReal) := hc.1.1
    have e2 : xk.1 ≤ ((89 : ℝ) : EReal) + ((6 : ℝ) : EReal) := hc.2.2
    by_cases htop : xk.1 = ⊤
    · rw [htop, ← EReal.coe_add] at e2
      exact absurd e2 (not_le.mpr (EReal.coe_lt_top _))
    by_cases hbot : xk.1 = ⊥
    · rw [hbot, EReal.bot_add] at e1
      exact absurd e1 (not_le.mpr (EReal.bot_lt_coe _))
    obtain ⟨x, hx⟩ : ∃ x : ℝ, xk.1 = ((x : ℝ) : EReal) :=
      ⟨xk.1.toReal, (EReal.coe_toReal htop hbot).symm⟩
    rw [hx, ← EReal.coe_add, EReal.coe_le_coe_iff] at e1
    rw [hx, ← EReal.coe_add, EReal.coe_le_coe_iff] at e2
    linarith

/-! ### The hypotheses are all satisfiable: `hDiag`, `hFin`, `hbox` -/

/-- `IsDiagramLike (mult r)` holds for EVERY rank `r`: by the definition of `mult`, a nonzero
value can only occur in the `(b, ⊥)` branch (where `⊥ < b`, as `b ≠ ⊥`) or the `d < b` branch
(where `d < b` already). -/
theorem isDiagramLike_mult (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  obtain ⟨b, d⟩ := p
  by_cases hb1 : b = ⊥
  · simp [mult, hb1] at hp
  by_cases hb2 : b = ⊤
  · simp [mult, hb2] at hp
  obtain ⟨br, rfl⟩ : ∃ br : ℝ, b = ((br : ℝ) : EReal) :=
    ⟨b.toReal, (EReal.coe_toReal hb2 hb1).symm⟩
  by_cases hd1 : d = ⊥
  · subst hd1; exact EReal.bot_lt_coe br
  by_cases hd2 : d = ⊤
  · subst hd2; simp [mult] at hp
  obtain ⟨dr, rfl⟩ : ∃ dr : ℝ, d = ((dr : ℝ) : EReal) :=
    ⟨d.toReal, (EReal.coe_toReal hd2 hd1).symm⟩
  unfold mult at hp
  simp only [EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_lt_coe_iff] at hp
  by_cases hdb : dr < br
  · exact EReal.coe_lt_coe_iff.mpr hdb
  · simp [hdb] at hp

/-- `mult rX ((b:ℝ), ⊥) = 0`: the `(b, ⊥)` probe always admits a death coordinate `t ≤ 89`
(and `≤ b - ε`), where `rX` reads `1` on both sides of the window. -/
theorem cex_multX_coe_bot (b : ℝ) :
    mult (rankFn cexStageX cexJX) (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [t45s_mult_coe_bot]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    t45s_zero_le _)
  refine iInf_le_of_le 1 (iInf_le_of_le (show (0 : ℝ) < 1 by norm_num)
    (iInf_le_of_le (min (b - 1) 0) (iInf_le_of_le (min_le_left (b - 1) 0) ?_)))
  have ht : min (b - 1) 0 ≤ 89 := le_trans (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 89)
  rw [cex_rankX_le89 (b - 1) (min (b - 1) 0) ht,
      cex_rankX_le89 (b + 1) (min (b - 1) 0) ht, tsub_self]

/-- `mult rX ((b:ℝ), (d:ℝ)) = 1` exactly at `(110, 89)`, `0` elsewhere (`d < b`). -/
theorem cex_multX_coe_coe_eq (b d : ℝ) (hbd : d < b) :
    mult (rankFn cexStageX cexJX) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) =
      if b = 110 ∧ d = 89 then 1 else 0 := by
  by_cases h110 : b = 110 ∧ d = 89
  · obtain ⟨rfl, rfl⟩ := h110
    rw [if_pos ⟨rfl, rfl⟩]
    exact cex_multX_coe_coe_110_89
  · rw [if_neg h110]
    rw [t45s_mult_coe_coe _ b d hbd]
    refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => t45s_zero_le _)
    -- Exhibit η with second-difference ≤ 0.
    by_cases hb : b = 110
    · -- b = 110, d ≠ 89, d < 110
      by_cases hd89 : d < 89
      · -- `89 < d + η` fails for small η  ⇒  first bracket 0
        obtain ⟨η, hpos, hηlt, hdη⟩ :
            ∃ η : ℝ, 0 < η ∧ η < (110 - d) / 2 ∧ d + η ≤ 89 := by
          refine ⟨min ((89 - d) / 2) ((110 - d) / 4), ?_, ?_, ?_⟩
          · exact lt_min (by linarith) (by linarith)
          · have := min_le_right ((89 - d) / 2) ((110 - d) / 4); linarith
          · have := min_le_left ((89 - d) / 2) ((110 - d) / 4); linarith
        have hmem : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := by rw [hb]; exact ⟨hpos, hηlt⟩
        refine iInf_le_of_le η (iInf_le_of_le hmem ?_)
        have ht1 : d + η ≤ b - η := by rw [hb]; linarith
        have ht2 : d - η ≤ b - η := by linarith
        rw [cex_diffX (b - η) (b + η) (d + η) (by linarith) ht1,
            if_neg (fun h => absurd h.2.2 (not_lt.mpr hdη)),
            cex_diffX (b - η) (b + η) (d - η) (by linarith) ht2, zero_tsub]
      · -- 89 < d < 110: both brackets 1 ⇒ 1 - 1 = 0
        have hdeq : d ≠ 89 := by intro hde; exact h110 ⟨hb, hde⟩
        have hdgt : 89 < d := lt_of_le_of_ne (le_of_not_gt hd89) (fun h => hdeq h.symm)
        obtain ⟨η, hpos, hηlt, hdη89⟩ :
            ∃ η : ℝ, 0 < η ∧ η < (110 - d) / 2 ∧ 89 < d - η := by
          refine ⟨min ((d - 89) / 2) ((110 - d) / 4), ?_, ?_, ?_⟩
          · exact lt_min (by linarith) (by linarith)
          · have := min_le_right ((d - 89) / 2) ((110 - d) / 4); linarith
          · have := min_le_left ((d - 89) / 2) ((110 - d) / 4); linarith
        have hmem : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := by rw [hb]; exact ⟨hpos, hηlt⟩
        refine iInf_le_of_le η (iInf_le_of_le hmem ?_)
        have ht1 : d + η ≤ b - η := by rw [hb]; linarith
        have ht2 : d - η ≤ b - η := by linarith
        have hs1 : b - η ≤ 110 := by rw [hb]; linarith
        have hs2 : 110 < b + η := by rw [hb]; linarith
        have h1a : 89 < d + η := by linarith
        rw [cex_diffX (b - η) (b + η) (d + η) (by linarith) ht1,
            if_pos ⟨hs1, hs2, h1a⟩,
            cex_diffX (b - η) (b + η) (d - η) (by linarith) ht2,
            if_pos ⟨hs1, hs2, hdη89⟩, tsub_self]
    · -- b ≠ 110: the window can avoid straddling 110 for small η ⇒ first bracket 0
      by_cases hblt : b < 110
      · obtain ⟨η, hpos, hηlt, hbη⟩ :
            ∃ η : ℝ, 0 < η ∧ η < (b - d) / 2 ∧ b + η ≤ 110 := by
          refine ⟨min ((110 - b) / 2) ((b - d) / 4), ?_, ?_, ?_⟩
          · exact lt_min (by linarith) (by linarith)
          · have := min_le_right ((110 - b) / 2) ((b - d) / 4); linarith
          · have := min_le_left ((110 - b) / 2) ((b - d) / 4); linarith
        have hmem : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := ⟨hpos, hηlt⟩
        refine iInf_le_of_le η (iInf_le_of_le hmem ?_)
        have ht1 : d + η ≤ b - η := by linarith
        have ht2 : d - η ≤ b - η := by linarith
        rw [cex_diffX (b - η) (b + η) (d + η) (by linarith) ht1,
            if_neg (fun h => absurd h.2.1 (not_lt.mpr hbη)),
            cex_diffX (b - η) (b + η) (d - η) (by linarith) ht2, zero_tsub]
      · -- 110 < b
        have hbgt : 110 < b := lt_of_le_of_ne (le_of_not_gt hblt) (fun h => hb h.symm)
        obtain ⟨η, hpos, hηlt, hbη⟩ :
            ∃ η : ℝ, 0 < η ∧ η < (b - d) / 2 ∧ 110 < b - η := by
          refine ⟨min ((b - 110) / 2) ((b - d) / 4), ?_, ?_, ?_⟩
          · exact lt_min (by linarith) (by linarith)
          · have := min_le_right ((b - 110) / 2) ((b - d) / 4); linarith
          · have := min_le_left ((b - 110) / 2) ((b - d) / 4); linarith
        have hmem : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := ⟨hpos, hηlt⟩
        refine iInf_le_of_le η (iInf_le_of_le hmem ?_)
        have ht1 : d + η ≤ b - η := by linarith
        have ht2 : d - η ≤ b - η := by linarith
        rw [cex_diffX (b - η) (b + η) (d + η) (by linarith) ht1,
            if_neg (fun h => absurd h.1 (not_le.mpr hbη)),
            cex_diffX (b - η) (b + η) (d - η) (by linarith) ht2, zero_tsub]

/-- The only nonzero point of `mult rX` is `((110, 89))`. -/
theorem cex_multX_support (p : EReal × EReal)
    (hp : mult (rankFn cexStageX cexJX) p ≠ 0) :
    p = (((110 : ℝ) : EReal), ((89 : ℝ) : EReal)) := by
  obtain ⟨b, d⟩ := p
  by_cases hb1 : b = ⊥
  · simp [mult, hb1] at hp
  by_cases hb2 : b = ⊤
  · simp [mult, hb2] at hp
  obtain ⟨br, rfl⟩ : ∃ br : ℝ, b = ((br : ℝ) : EReal) :=
    ⟨b.toReal, (EReal.coe_toReal hb2 hb1).symm⟩
  by_cases hd1 : d = ⊥
  · subst hd1; exact absurd (cex_multX_coe_bot br) hp
  by_cases hd2 : d = ⊤
  · subst hd2; simp [mult] at hp
  obtain ⟨dr, rfl⟩ : ∃ dr : ℝ, d = ((dr : ℝ) : EReal) :=
    ⟨d.toReal, (EReal.coe_toReal hd2 hd1).symm⟩
  by_cases hdb : dr < br
  · have heq := cex_multX_coe_coe_eq br dr hdb
    rw [heq] at hp
    by_cases h : br = 110 ∧ dr = 89
    · rw [if_pos h] at hp
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · rw [if_neg h] at hp; simp at hp
  · unfold mult at hp
    simp [EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_lt_coe_iff, hdb] at hp

theorem cex_hDiagX : IsDiagramLike (mult (rankFn cexStageX cexJX)) := isDiagramLike_mult _
theorem cex_hDiagY : IsDiagramLike (mult (rankFn cexStageY cexJY)) := isDiagramLike_mult _

theorem cex_hFinY : {p : EReal × EReal | mult (rankFn cexStageY cexJY) p ≠ 0}.Finite := by
  have h : ∀ p, ¬ (mult (rankFn cexStageY cexJY) p ≠ 0) := fun p hp => hp (cex_multY_zero p)
  exact Set.finite_empty.subset (fun p hp => absurd hp (h p))

theorem cex_hFinX : {p : EReal × EReal | mult (rankFn cexStageX cexJX) p ≠ 0}.Finite := by
  have hsub : {p : EReal × EReal | mult (rankFn cexStageX cexJX) p ≠ 0}
      ⊆ ({(((110 : ℝ) : EReal), ((89 : ℝ) : EReal))} : Set (EReal × EReal)) := by
    intro p hp; exact cex_multX_support p hp
  exact (Set.finite_singleton _).subset hsub

/-! ### The box-expansion hypothesis `hbox` holds at `α = 0`, `ε = 6` -/

theorem cex_rY_ge_one (s t : ℝ) : 1 ≤ rankFn cexStageY cexJY s t := by
  by_cases h : t ≤ 94
  · rw [cex_rankY_le s t h]
  · rw [cex_rankY_gt s t (not_le.mp h)]; decide

theorem cex_rX_ge_one (s t : ℝ) (hst : t ≤ s) : 1 ≤ rankFn cexStageX cexJX s t := by
  by_cases h89 : t ≤ 89
  · rw [cex_rankX_le89 s t h89]
  · have h89' : 89 < t := not_le.mp h89
    by_cases h100 : t ≤ 100
    · by_cases hs110 : s ≤ 110
      · rw [cex_rankX_mid_le s t h89' h100 hs110]; decide
      · rw [cex_rankX_mid_gt s t h89' h100 (not_le.mp hs110)]
    · have h100' : 100 < t := not_le.mp h100
      by_cases hs110 : s ≤ 110
      · rw [cex_rankX_gt100_le s t h100' hst hs110]; decide
      · rw [cex_rankX_gt100_gt s t h100' (not_le.mp hs110)]; decide

/-- The box-expansion inequalities of the child lemma HOLD for the two counterexample modules
at `α = 0`, `ε = 6`. -/
theorem cex_hbox : ∀ s t : ℝ, t + 2 * 6 ≤ s →
    truncRank (rankFn cexStageX cexJX) 0 s t ≤
      truncRank (rankFn cexStageY cexJY) 0 (s - 6) (t + 6) ∧
    truncRank (rankFn cexStageY cexJY) 0 s t ≤
      truncRank (rankFn cexStageX cexJX) 0 (s - 6) (t + 6) := by
  intro s t h
  by_cases ht0 : t < 0
  · refine ⟨?_, ?_⟩
    · rw [t45s_truncRank_zero_of_lt (rankFn cexStageX cexJX) 0 s t ht0]; exact t45s_zero_le _
    · rw [t45s_truncRank_zero_of_lt (rankFn cexStageY cexJY) 0 s t ht0]; exact t45s_zero_le _
  · have h0t : 0 ≤ t := le_of_not_gt ht0
    have hs12 : 0 ≤ s := by linarith
    have hs6 : 0 ≤ s - 6 := by linarith
    have ht6 : 0 ≤ t + 6 := by linarith
    have hle : t + 6 ≤ s - 6 := by linarith
    rw [t45s_truncRank_eq (rankFn cexStageX cexJX) 0 s t hs12 h0t,
        t45s_truncRank_eq (rankFn cexStageY cexJY) 0 (s - 6) (t + 6) hs6 ht6,
        t45s_truncRank_eq (rankFn cexStageY cexJY) 0 s t hs12 h0t,
        t45s_truncRank_eq (rankFn cexStageX cexJX) 0 (s - 6) (t + 6) hs6 ht6]
    constructor
    · -- rX s t ≤ rY (s-6) (t+6)
      by_cases h89 : t ≤ 89
      · rw [cex_rankX_le89 s t h89]; exact cex_rY_ge_one (s - 6) (t + 6)
      · have h89' : 89 < t := not_le.mp h89
        by_cases h100 : t ≤ 100
        · by_cases hs110 : s ≤ 110
          · rw [cex_rankX_mid_le s t h89' h100 hs110,
                cex_rankY_gt (s - 6) (t + 6) (by linarith : (94 : ℝ) < t + 6)]
          · rw [cex_rankX_mid_gt s t h89' h100 (not_le.mp hs110)]
            exact cex_rY_ge_one (s - 6) (t + 6)
        · have h100' : 100 < t := not_le.mp h100
          have hs110 : 110 < s := by linarith
          rw [cex_rankX_gt100_gt s t h100' hs110,
              cex_rankY_gt (s - 6) (t + 6) (by linarith : (94 : ℝ) < t + 6)]
    · -- rY s t ≤ rX (s-6) (t+6)
      by_cases h94 : t ≤ 94
      · rw [cex_rankY_le s t h94]; exact cex_rX_ge_one (s - 6) (t + 6) hle
      · have h94' : 94 < t := not_le.mp h94
        rw [cex_rankY_gt s t h94']
        by_cases hs'110 : s - 6 ≤ 110
        · rw [cex_rankX_gt100_le (s - 6) (t + 6) (by linarith : (100 : ℝ) < t + 6) hle hs'110]
          decide
        · rw [cex_rankX_gt100_gt (s - 6) (t + 6) (by linarith : (100 : ℝ) < t + 6)
              (not_le.mp hs'110)]

/-! ### The theorem, negated -/

/-- **The child lemma `theorem_4_5_lemma_4_6_corrected_stability` is FALSE.**

All its hypotheses hold for the modules `X` (`Fin 3`) and `Y` (`Fin 2`) at `α = 0`, `ε = 6`
(`FiltrationLaw`, `hbox`, diagram-likeness, finite support), yet the asserted multi-bijection
cannot exist: `mult (truncRank rY 0) ≡ 0` leaves no target for the X-copy at `(110, 89)`.

The statement below is the child's content over modules in `Type` (the counterexample lives in
`Fin 3`/`Fin 2`). The paper's `hero` statement is universe-polymorphic (`{ιX : Type*}`); Lean
cannot instantiate a universe-parameter to `Type 0` without lifting the modules, but the failure
at `Type` is what refutes the mathematical claim (and, morally, every universe). -/
theorem theorem_4_5_lemma_4_6_corrected_stability_is_false :
    ¬ ∀ (ιX ιY : Type) (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
      (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
      (α ε : ℝ) (hε : 0 ≤ ε)
      (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
      (hbox : ∀ s t : ℝ, t + 2 * ε ≤ s →
        truncRank (rankFn stageX JX) α s t ≤ truncRank (rankFn stageY JY) α (s - ε) (t + ε) ∧
        truncRank (rankFn stageY JY) α s t ≤ truncRank (rankFn stageX JX) α (s - ε) (t + ε))
      (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
      (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
      (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
      (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite),
      ∃ δ : Copies (mult (truncRank (rankFn stageX JX) α))
          ≃ Copies (mult (truncRank (rankFn stageY JY) α)),
        (∀ a, closeE (pt a).1 (pt (δ a)).1 ε ∧ closeE (pt a).2 (pt (δ a)).2 ε) ∧
        (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 ε ∧ closeE (pt (δ.symm b)).2 (pt b).2 ε) := by
  intro H
  exact cex_no_matching (H (Fin 3) (Fin 2) cexStageX cexJX cexStageY cexJY 0 6
    (by norm_num : (0 : ℝ) ≤ 6)
    cex_hLawX cex_hLawY cex_hbox cex_hDiagX cex_hDiagY cex_hFinX cex_hFinY)

/-! ## Platform disproof form (a verified proof of the negation of the target type)

`solution` below proves the negation of the published statement of
`PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability` (verbatim binder list and
conclusion, negated). The type variables are fixed at universe 0 (`Type`), the universe of the
explicit counterexample instance: module X over `Fin 3`, module Y over `Fin 2`, truncation
level `α = 0`, radius `ε = 6`. Since the published theorem is universe-polymorphic, refuting
its universe-0 restriction refutes it. All hypotheses hold at the instance (the named theorems
`cex_hLawX` … `cex_hFinY` above, including the box-expansion `cex_hbox`) and the asserted
multi-bijection is impossible there (`cex_no_matching`). -/

set_option maxHeartbeats 2000000 in
/-- DISPROOF of `theorem_4_5_lemma_4_6_corrected_stability`: the negation of its full published
statement (at universe 0, where the explicit counterexample of this file lives — module X on
`Fin 3` with two `⊤`-born points merging at 100 plus a point born at 110 dying at 89; module Y
on `Fin 2` with two `⊤`-born points merging at 94). Every hypothesis holds at the instance —
genuine `FiltrationLaw` modules, the `α = 0`, `ε = 6` box-expansion interleaving of the
truncated ranks (`cex_hbox`) — yet the asserted multi-bijection of truncated copies fails:
X's truncated diagram is `{(110, 89)}` while Y's is empty, so X's off-diagonal copy has no
`6`-close partner (`cex_no_matching`). Root cause: classes born at `+∞` are invisible to
`mult` yet inflate truncated ranks. -/

theorem solution : ¬ ∀ {ιX : Type} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hbox : ∀ s t : ℝ, t + 2 * ε ≤ s →
      truncRank (rankFn stageX JX) α s t ≤ truncRank (rankFn stageY JY) α (s - ε) (t + ε) ∧
      truncRank (rankFn stageY JY) α s t ≤ truncRank (rankFn stageX JX) α (s - ε) (t + ε))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite),
    ∃ δ : Copies (mult (truncRank (rankFn stageX JX) α))
        ≃ Copies (mult (truncRank (rankFn stageY JY) α)),
      (∀ a, closeE (pt a).1 (pt (δ a)).1 ε ∧ closeE (pt a).2 (pt (δ a)).2 ε) ∧
      (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 ε ∧ closeE (pt (δ.symm b)).2 (pt b).2 ε) := by
  intro h
  exact cex_no_matching
    (h cexStageX cexJX cexStageY cexJY 0 6 (by norm_num : (0 : ℝ) ≤ 6)
      cex_hLawX cex_hLawY cex_hbox cex_hDiagX cex_hDiagY cex_hFinX cex_hFinY)
