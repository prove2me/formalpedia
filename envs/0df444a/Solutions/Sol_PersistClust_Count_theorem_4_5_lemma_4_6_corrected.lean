-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_lemma_4_6_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T14:12:16.407976+00:00
-- url     : https://prove2.me/submissions/594719b7-3fb8-4ad9-9c12-7dcb8c9cfcbe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank
import Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_mult_agree
import Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_stability
import Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_surgery

open PersistClust.Count

/-!
# Corrected Lemma 4.6 — algebraic stability for 0-dim persistence modules as rankFn + FiltrationLaw

Reduction of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected` to three decomposition children.

Proof route (Appendix A of RR-6968, Addendum-4 repair recipe):
  0. TRUNCATE both modules at `α` (Eq. 16): `truncRank r α s t = r s t` when both windows
     are `≥ α`, else `0` (the truncated module `X̃` is `0` below `α`, so any map landing in
     or leaving the zero module has rank `0`).  `truncRank` is the shared Definition
     `PersistClust.Count.truncRank` (Def_PersistClust_Count_TruncRank).
  1. The box-expansion inequalities (hypothesis `hbx`, guard `t + 2ε ≤ s ∧ α ≤ t`) transfer
     to the truncated pair as box inequalities with NO `α` guard: below `α` the truncated
     source rank is `0` (trivial); above `α` it equals the original rank and the shifted
     window `(s-ε, t+ε)` also lies above `α` (`α ≤ t ≤ t+ε` and `α ≤ t ≤ t+2ε ≤ s ⇒ α ≤ s-ε`),
     so `hbx` applies verbatim.  **Proved inline** as `box_expansion_truncated_global`.
  2. Ranks agree with truncated ranks for `s ≥ t ≥ α` (Eq. 18) ⇒ diagrams agree on `QNE_α`.
     **Child** `theorem_4_5_lemma_4_6_corrected_mult_agree` (η-grid Eqs. 19–22 cancellation).
  3. Global algebraic stability on the truncated pair ⇒ bijection `δ` with `L∞`-`ε` control.
     **Child** `theorem_4_5_lemma_4_6_corrected_stability` (Extended Stability, Appendix A core).
  5. SURGERY: compose the truncated stability bijection with the identity on `QNE_α` via the
     vertical per-birth matching; verify assertions (i)–(iv) of `SatisfiesIIV`.
     **Child** `theorem_4_5_lemma_4_6_corrected_surgery` (death-crossing subtlety resolved by
     the ε-proximal vertical per-birth matching).

Also proved inline: `trunc_rank_eq_above_α` (Eq. 18, used implicitly by child 2/3) and the
universal `isDiagramLike_mult` (`IsDiagramLike (mult r)` for every `r`, discharging every
diagram-like hypothesis, including the truncated diagrams).
-/

namespace T45AlgCorrected

/-- `truncRank` agrees with `r` once both windows are at or above `α` (Eq. 18). -/
theorem trunc_rank_eq_above_α
    (r : ℝ → ℝ → ℕ∞) (a : ℝ) {s t : ℝ} (hs : a ≤ s) (ht : a ≤ t) :
    truncRank r a s t = r s t := by
  show (if a ≤ s ∧ a ≤ t then r s t else 0) = r s t
  exact if_pos (And.intro hs ht)

/-- `IsDiagramLike (mult r)` holds for EVERY rank function `r`. By the definition of `mult`,
a point of positive multiplicity must lie in one of the two nonzero branches: either
`p.2 = ⊥` (then `⊥ < p.1` since the outer guard forces `p.1 ≠ ⊥`), or `p.2 < p.1` directly.
All other branches yield `0`. Hence the `IsDiagramLike` hypotheses of the target — and those
for the *truncated* diagrams — are free. -/
theorem isDiagramLike_mult (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
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

/-- Step 1 (proved): the box-expansion inequalities valid above `α` with guard `t + 2ε ≤ s`
become box inequalities for the truncated pair with NO `α` guard. -/
theorem box_expansion_truncated_global
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hbx : ∀ s t : ℝ, t + 2 * ε ≤ s → α ≤ t →
      rankFn stageX JX s t ≤ rankFn stageY JY (s - ε) (t + ε) ∧
      rankFn stageY JY s t ≤ rankFn stageX JX (s - ε) (t + ε)) :
    ∀ s t : ℝ, t + 2 * ε ≤ s →
      truncRank (rankFn stageX JX) α s t ≤ truncRank (rankFn stageY JY) α (s - ε) (t + ε) ∧
      truncRank (rankFn stageY JY) α s t ≤ truncRank (rankFn stageX JX) α (s - ε) (t + ε) := by
  intro s t hst
  have hts : α ≤ t → α ≤ s := fun ht => by linarith
  have hte : α ≤ t → α ≤ t + ε := fun ht => by linarith
  have hse : α ≤ t → α ≤ s - ε := fun ht => by linarith
  refine ⟨?_, ?_⟩
  · by_cases ht : α ≤ t
    · have hx : truncRank (rankFn stageX JX) α s t = rankFn stageX JX s t := by
        show (if α ≤ s ∧ α ≤ t then rankFn stageX JX s t else 0) = rankFn stageX JX s t
        exact if_pos (And.intro (hts ht) ht)
      have hy : truncRank (rankFn stageY JY) α (s - ε) (t + ε) =
          rankFn stageY JY (s - ε) (t + ε) := by
        show (if α ≤ s - ε ∧ α ≤ t + ε then rankFn stageY JY (s - ε) (t + ε) else 0)
            = rankFn stageY JY (s - ε) (t + ε)
        exact if_pos (And.intro (hse ht) (hte ht))
      rw [hx, hy]; exact (hbx s t hst ht).1
    · have hx : truncRank (rankFn stageX JX) α s t = 0 := by
        show (if α ≤ s ∧ α ≤ t then rankFn stageX JX s t else 0) = 0
        exact if_neg (fun h => ht h.2)
      rw [hx]; exact zero_le
  · by_cases ht : α ≤ t
    · have hy : truncRank (rankFn stageY JY) α s t = rankFn stageY JY s t := by
        show (if α ≤ s ∧ α ≤ t then rankFn stageY JY s t else 0) = rankFn stageY JY s t
        exact if_pos (And.intro (hts ht) ht)
      have hx : truncRank (rankFn stageX JX) α (s - ε) (t + ε) =
          rankFn stageX JX (s - ε) (t + ε) := by
        show (if α ≤ s - ε ∧ α ≤ t + ε then rankFn stageX JX (s - ε) (t + ε) else 0)
            = rankFn stageX JX (s - ε) (t + ε)
        exact if_pos (And.intro (hse ht) (hte ht))
      rw [hy, hx]; exact (hbx s t hst ht).2
    · have hy : truncRank (rankFn stageY JY) α s t = 0 := by
        show (if α ≤ s ∧ α ≤ t then rankFn stageY JY s t else 0) = 0
        exact if_neg (fun h => ht h.2)
      rw [hy]; exact zero_le

end T45AlgCorrected

/-! ## Target statement (binders VERBATIM from the stub) — reduction to the 3 children. -/

theorem solution
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hbx : ∀ s t : ℝ, t + 2 * ε ≤ s → α ≤ t →
      rankFn stageX JX s t ≤ rankFn stageY JY (s - ε) (t + ε) ∧
      rankFn stageY JY s t ≤ rankFn stageX JX (s - ε) (t + ε))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite) :
    ∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ α ε := by
  -- Step 1: box-expansion transfers to the truncated pair (no α guard).
  have hbox :=
    T45AlgCorrected.box_expansion_truncated_global stageX JX stageY JY α ε hε hbx
  -- Step 2: diagram agreement on QNE_α for each module (child: mult_agree).
  have hAgree : ∀ p ∈ QNE α,
      mult (rankFn stageX JX) p = mult (truncRank (rankFn stageX JX) α) p ∧
      mult (rankFn stageY JY) p = mult (truncRank (rankFn stageY JY) α) p :=
    fun p hp =>
      ⟨theorem_4_5_lemma_4_6_corrected_mult_agree stageX JX hLawX α hFinX p hp,
       theorem_4_5_lemma_4_6_corrected_mult_agree stageY JY hLawY α hFinY p hp⟩
  -- Step 3: global stability on the truncated pair gives δ with L∞-ε control (child: stability).
  have hδ :=
    theorem_4_5_lemma_4_6_corrected_stability
      stageX JX stageY JY α ε hε hLawX hLawY hbox hDiagX hDiagY hFinX hFinY
  -- Step 5: surgery + composition yields γ satisfying assertions (i)–(iv) (child: surgery).
  exact
    theorem_4_5_lemma_4_6_corrected_surgery
      stageX JX stageY JY α ε hε hLawX hLawY hDiagX hDiagY hFinX hFinY hAgree hδ
