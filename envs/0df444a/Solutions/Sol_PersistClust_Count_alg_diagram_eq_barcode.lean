-- Prove2me | solution 1 for PersistClust.Count.alg_diagram_eq_barcode
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T11:11:29.481163+00:00
-- url     : https://prove2.me/submissions/a75ab452-0b52-4d78-bcd9-17fe2988e4c1

import Mathlib
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_AlgBarcode
import Theorems.Thm_PersistClust_Count_alg_diagram_immortal_pair
import Theorems.Thm_PersistClust_Count_alg_diagram_death_pair
import Theorems.Thm_PersistClust_Count_alg_diagram_barcode_support

/-!
# Reduction: `alg_diagram_eq_barcode` to three child lemmas

The pointwise equality `ripsDiagram Dm g δ = ripsBarcode g Dm δ σ` (Eq. (3) of RR-6968:
the analytic 0-th persistence diagram of the upper-star Rips filtration — `mult (ripsRank …)`
— coincides with the elder-rule barcode of Procedure 1 at merge threshold `τ = +∞`) splits,
at a point `(b, d)` of the extended plane, into three independent children:

1. `alg_diagram_immortal_pair` — the **immortal slice**: for every *real* birth level `b`,
   both sides agree at `(b, ⊥)`. (Analytically both count the connected components of the
   full Rips graph `R_δ` whose highest-`g` vertex has value `b` — the entries surviving the
   whole sweep, one immortal bar each.)
2. `alg_diagram_death_pair` — the **finite-death slice**: for all real `d < b`, both sides
   agree at `(b, d)`. (Analytically both are the elder-rule pairs born in the `b`-window and
   dying in the `d`-window; off critical values both are `0`.)
3. `alg_diagram_barcode_support` — the **zero-mass side**: every point at which the barcode
   is nonzero has real birth `= g r` for some vertex `r`, and its death coordinate is either
   `⊥` (immortal) or a real level strictly below the birth level (off-diagonal pair).

Assembly (below): `funext` and case analysis on the point `p = (pb, pd) ∈ EReal × EReal`.
- If `pb` is not a real level (`⊥` or `⊤`), `mult` lands in its outer else-branch (`0`), and
  child 3 (contrapositive) kills the barcode, since `⊥`/`⊤` cannot be a `(g r : EReal)`.
- If `pb = (b : EReal)` is real and `pd = ⊥`, child 1 applies for every real `b` (no grid
  restriction is needed: both sides vanish when `b` is not a vertex value).
- If `pb = (b : EReal)` is real and `pd = (d : EReal)` is real:
  * `d < b`: child 2 applies (again for *all* real `d < b`; when `d` is not a vertex value
    both sides are `0`).
  * `b ≤ d`: the `mult` branch condition `p.2 < p.1` fails, so `mult = 0`; the barcode is
    `0` by child 3, whose conclusion forces a real death `d < g r = b` or birth `⊥` —
    impossible when `p.2 = (d : EReal)` with `b ≤ d`.
- If `pb = (b : EReal)` is real and `pd = ⊤`: `mult`'s `p.2 < p.1` fails (`0`), and child 3
  (contrapositive) kills the barcode, since `⊤` is neither `⊥` nor a real coercion.

The three children are exactly the standard decomposition of the
"persistence diagram of a finite superlevel filtration equals its elder-rule barcode"
theorem into the essential-class slice, the finite-interval slice, and the off-support
control. Each is faithful to RR-6968, Procedure 1–2 and Eq. (3), and was validated by
brute-force simulation (`n ≤ 5` exhaustive + random, with faithful evaluation of the
`mult` infima).
-/

open PersistClust.Count

/-! ### Auxiliary: the `mult` of any rank function is `0` on the zero-mass regions --/

/-- `mult r (⊥, pd) = 0`: the outer condition `p.1 ≠ ⊥` fails. -/
lemma algD_mult_zero_birth_bot (r : ℝ → ℝ → ℕ∞) (pd : EReal) :
    mult r (⊥, pd) = 0 := by
  have h : ¬((⊥ : EReal) ≠ ⊥ ∧ (⊥ : EReal) ≠ ⊤) := fun hh => hh.1 rfl
  unfold mult
  dsimp only
  rw [if_neg h]

/-- `mult r (⊤, pd) = 0`: the outer condition `p.1 ≠ ⊤` fails. -/
lemma algD_mult_zero_birth_top (r : ℝ → ℝ → ℕ∞) (pd : EReal) :
    mult r (⊤, pd) = 0 := by
  have h : ¬((⊤ : EReal) ≠ ⊥ ∧ (⊤ : EReal) ≠ ⊤) := fun hh => hh.2 rfl
  unfold mult
  dsimp only
  rw [if_neg h]

/-- `mult r ((b : EReal), ⊤) = 0`: the death-coordinate is `⊤`, so neither inner branch fires. -/
lemma algD_mult_zero_topdeath (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r ((b : EReal), ⊤) = 0 := by
  have hne_bot : ((b : EReal)) ≠ ⊥ := EReal.coe_ne_bot b
  have hne_top : ((b : EReal)) ≠ ⊤ := EReal.coe_ne_top b
  have hpd_ne_bot : ¬(⊤ = (⊥ : EReal)) := fun hh => by contradiction
  have hpd_lt : ¬((⊤ : EReal) < ((b : EReal))) := fun hh => not_top_lt hh
  unfold mult
  dsimp only
  rw [if_pos ⟨hne_bot, hne_top⟩, if_neg hpd_ne_bot, if_neg hpd_lt]

/-- `mult r ((b : EReal), (d : EReal)) = 0` when `b ≤ d`: the branch `p.2 < p.1` fails. -/
lemma algD_mult_zero_diag (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (h : b ≤ d) :
    mult r ((b : EReal), (d : EReal)) = 0 := by
  have hne_bot : ((b : EReal)) ≠ ⊥ := EReal.coe_ne_bot b
  have hne_top : ((b : EReal)) ≠ ⊤ := EReal.coe_ne_top b
  have hpd_ne_bot : ¬(((d : EReal)) = (⊥ : EReal)) := fun hh => EReal.coe_ne_bot d hh
  have hnb : ¬(d < b) := not_lt.mpr h
  have hpd_lt : ¬(((d : EReal)) < ((b : EReal))) := fun hh => hnb (EReal.coe_lt_coe_iff.mp hh)
  unfold mult
  dsimp only
  rw [if_pos ⟨hne_bot, hne_top⟩, if_neg hpd_ne_bot, if_neg hpd_lt]

/-- The barcode is `0` at a point whose birth coordinate cannot equal any `(g r : EReal)`. -/
lemma algD_barcode_zero_of_birth_notin (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (pb pd : EReal)
    (hpb : ∀ r : Fin n, pb ≠ ((g r : EReal))) :
    ripsBarcode g Dm δ σ (pb, pd) = 0 := by
  by_contra hp
  obtain ⟨r, hr, _⟩ := alg_diagram_barcode_support n g Dm δ σ (pb, pd) hp
  exact hpb r hr

theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) :
    ripsDiagram Dm g δ = ripsBarcode g Dm δ σ := by
  funext p
  obtain ⟨pb, pd⟩ := p
  by_cases hbot : pb = ⊥
  · -- birth coordinate `⊥`: `mult` is `0`; barcode is `0` (no `g r` equals `⊥`).
    rw [hbot]
    have hL : ripsDiagram Dm g δ (⊥, pd) = 0 := by
      show mult (ripsRank Dm g δ) (⊥, pd) = 0
      exact algD_mult_zero_birth_bot (ripsRank Dm g δ) pd
    have hR : ripsBarcode g Dm δ σ (⊥, pd) = 0 :=
      algD_barcode_zero_of_birth_notin n g Dm δ σ ⊥ pd
        (fun r => (EReal.coe_ne_bot (g r)).symm)
    rw [hL, hR]
  · by_cases htop : pb = ⊤
    · -- birth coordinate `⊤`: `mult` is `0`; barcode is `0` (no `g r` equals `⊤`).
      rw [htop]
      have hL : ripsDiagram Dm g δ (⊤, pd) = 0 := by
        show mult (ripsRank Dm g δ) (⊤, pd) = 0
        exact algD_mult_zero_birth_top (ripsRank Dm g δ) pd
      have hR : ripsBarcode g Dm δ σ (⊤, pd) = 0 :=
        algD_barcode_zero_of_birth_notin n g Dm δ σ ⊤ pd
          (fun r => (EReal.coe_ne_top (g r)).symm)
      rw [hL, hR]
    · -- birth coordinate is real: replace `pb` by its coercion.
      have hb : ((pb.toReal : EReal)) = pb := EReal.coe_toReal htop hbot
      rw [← hb]
      by_cases hpd_bot : pd = ⊥
      · -- real birth, immortal death: child 1.
        rw [hpd_bot]
        exact alg_diagram_immortal_pair n g Dm hDm δ σ hσ pb.toReal
      · by_cases hpd_top : pd = ⊤
        · -- real birth, `⊤` death: both sides vanish.
          rw [hpd_top]
          have hL : ripsDiagram Dm g δ (((pb.toReal : EReal)), ⊤) = 0 := by
            show mult (ripsRank Dm g δ) (((pb.toReal : EReal)), ⊤) = 0
            exact algD_mult_zero_topdeath (ripsRank Dm g δ) pb.toReal
          have hR : ripsBarcode g Dm δ σ (((pb.toReal : EReal)), ⊤) = 0 := by
            by_contra hp
            obtain ⟨r, hr, hdis⟩ :=
              alg_diagram_barcode_support n g Dm δ σ (((pb.toReal : EReal)), ⊤) hp
            rcases hdis with h1 | ⟨d, h2, -⟩
            · exact absurd h1 (by contradiction)
            · exact EReal.coe_ne_top d h2.symm
          rw [hL, hR]
        · -- death coordinate is real: replace `pd` by its coercion.
          have hd : ((pd.toReal : EReal)) = pd := EReal.coe_toReal hpd_top hpd_bot
          rw [← hd]
          by_cases hlt : pd.toReal < pb.toReal
          · -- real `d < b`: child 2.
            exact alg_diagram_death_pair n g Dm hDm δ σ hσ pb.toReal pd.toReal hlt
          · -- real `b ≤ d`: `mult = 0`, and child 3 kills the barcode.
            have hle : pb.toReal ≤ pd.toReal := not_lt.mp hlt
            have hL : ripsDiagram Dm g δ ((pb.toReal : EReal), (pd.toReal : EReal)) = 0 := by
              show mult (ripsRank Dm g δ) ((pb.toReal : EReal), (pd.toReal : EReal)) = 0
              exact algD_mult_zero_diag (ripsRank Dm g δ) pb.toReal pd.toReal hle
            have hR : ripsBarcode g Dm δ σ ((pb.toReal : EReal), (pd.toReal : EReal)) = 0 := by
              by_contra hp
              obtain ⟨r, hr, hdis⟩ :=
                alg_diagram_barcode_support n g Dm δ σ
                  ((pb.toReal : EReal), (pd.toReal : EReal)) hp
              have hbr : pb.toReal = g r :=
                EReal.coe_injective (by simpa using hr)
              rcases hdis with h1 | ⟨d', hd', hdlt⟩
              · exact EReal.coe_ne_bot pd.toReal h1
              · have hdd : pd.toReal = d' := EReal.coe_injective hd'
                have hdlt' : d' < g r := EReal.coe_lt_coe_iff.mp hdlt
                have hchain : d' < pb.toReal := by rw [hbr]; exact hdlt'
                have hle' : pb.toReal ≤ d' := by rw [← hdd]; exact hle
                exact absurd (lt_of_lt_of_le hchain hle') (lt_irrefl d')
            rw [hL, hR]
