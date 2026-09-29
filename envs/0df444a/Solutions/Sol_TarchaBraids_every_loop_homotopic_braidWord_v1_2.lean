-- Prove2me | solution 2 for TarchaBraids.every_loop_homotopic_braidWord_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-28T00:50:28.70547+00:00
-- url     : https://prove2.me/submissions/e95ac772-57bb-4a19-9e88-1c422dc1ba0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TarchaBraids_thm_3_11_half_twists_generate
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1

/-!
# Assembly spec: TarchaBraids.every_loop_homotopic_braidWord_v1 (path-level normal form)

Theorem id: 0fa0a598-6b37-4d0f-a8f0-f491f0b924bb
Status at spec time (2026-09-28 ~08:50 +08, live-verified): Open, deprecated_at = null.
Prior submission: fba6856d-ae60-4294-b098-c801dfbce212 (SKETCH_ACCEPTED, 2026-09-21).

## Dependency tree (all live-verified 2026-09-28)

  0fa0a598  every_loop_homotopic_braidWord_v1          Open   <-- THIS FILE
    |  bridge below: aec3d1f1 ==> 0fa0a598 (elementary:
    |  wordSubgroup + wordLoop_class + Quotient.exact; no topology)
    v
  aec3d1f1  TarchaBraids.thm_3_11_half_twists_generate  Open   <-- BLOCKER
    : Subgroup.closure (Set.range fun i : Fin (n-1) => halfTwistBraid n i) = ⊤
    |  Fadell-Neuwirth induction; 2x SKETCH_ACCEPTED, never proved
    v
  7b08a659  puncturedPlaneGroup_free_on_standardGen     Open   (sketch only)
  613636f7  standardGen_image_mem_halfTwist             Open   (sketch only)
  02bcc504  fadellNeuwirth_ker_image_le_halfTwist       Open   (sketch only)
  142bee4a  fadellNeuwirth_ker_le_range                 PROVED (in-mission)

## Verdict ceiling

The bridge below is machine-verified to elaborate: the 2026-09-21 submission of
this exact assembly returned SKETCH_ACCEPTED (elaborated, sorry-free), capped
solely on aec3d1f1 being Open. Resubmitting before aec3d1f1 is Proved buys
another zero-point sketch -- DO NOT SUBMIT until the blocker lands.

## Unblock condition

When aec3d1f1 (TarchaBraids.thm_3_11_half_twists_generate) is Proved, submit
this file verbatim: the only cited Theorems.Thm_* stub will then be Proved and
the verdict ceiling lifts to ACCEPTED. Solve-now targets are the three Open
Fadell-Neuwirth leaves above (7b08a659, 613636f7, 02bcc504).

## Provenance

Bridge adapted from submission fba6856d (server-elaborated 2026-09-21).
`theorem solution` is top-level (gate 1b/1c); `set_option autoImplicit false`
matches the server's elaboration settings.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option autoImplicit false

open BraidsLinksMCG TarchaBraids

namespace WordSol

variable (n : ℕ)

/-- The braid group element named by a signed letter. -/
noncomputable def letterBraid (a : BraidLetter n) : GeomBraidGroup n :=
  match a.sign with
  | .positive => halfTwistBraid n a.index
  | .negative => (halfTwistBraid n a.index)⁻¹

lemma letterLoop_class (a : BraidLetter n) :
    FundamentalGroup.fromPath (⟦braidLetterLoop n a⟧ :
      Path.Homotopic.Quotient (baseUnordered n) (baseUnordered n)) = letterBraid n a := by
  cases h : a.sign <;> simp only [letterBraid, braidLetterLoop, h] <;> rfl

lemma wordLoop_class (w : List (BraidLetter n)) :
    FundamentalGroup.fromPath (⟦braidWordLoop n w⟧ :
      Path.Homotopic.Quotient (baseUnordered n) (baseUnordered n))
      = (w.map (letterBraid n)).prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show FundamentalGroup.fromPath
      (⟦(braidWordLoop n w).trans (braidLetterLoop n a)⟧ : Path.Homotopic.Quotient _ _) = _
    rw [List.map_cons, List.prod_cons, ← ih, ← letterLoop_class n a]
    rfl

/-- Flip the sign of a letter. -/
def flipLetter (a : BraidLetter n) : BraidLetter n :=
  ⟨a.index, match a.sign with | .positive => .negative | .negative => .positive⟩

lemma letterBraid_flip (a : BraidLetter n) :
    letterBraid n (flipLetter n a) = (letterBraid n a)⁻¹ := by
  cases h : a.sign <;> simp [letterBraid, flipLetter, h]

/-- The elements nameable by a finite signed half-twist word form a subgroup. -/
noncomputable def wordSubgroup : Subgroup (GeomBraidGroup n) where
  carrier := {g | ∃ w : List (BraidLetter n), (w.map (letterBraid n)).prod = g}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro a b ⟨w1, rfl⟩ ⟨w2, rfl⟩
    exact ⟨w1 ++ w2, by rw [List.map_append, List.prod_append]⟩
  inv_mem' := by
    rintro a ⟨w, rfl⟩
    refine ⟨(w.map (flipLetter n)).reverse, ?_⟩
    rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
    congr 2
    exact List.map_congr_left fun b _ => letterBraid_flip n b

lemma closure_le_wordSubgroup :
    Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i))
      ≤ wordSubgroup n := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨i, rfl⟩
  exact ⟨[⟨i, .positive⟩], by simp [letterBraid]⟩

/-- THE BRIDGE: group-theoretic generation implies the path-level normal form.
The only non-elementary input is `TarchaBraids.thm_3_11_half_twists_generate`
(aec3d1f1, currently Open) - everything else is proved here from the
definitions and Mathlib. -/
theorem every_loop (n : ℕ) : EveryLoopHasBraidWord n := by
  intro γ
  have hmem : FundamentalGroup.fromPath
      (⟦γ⟧ : Path.Homotopic.Quotient (baseUnordered n) (baseUnordered n))
      ∈ wordSubgroup n := by
    refine closure_le_wordSubgroup n ?_
    rw [TarchaBraids.thm_3_11_half_twists_generate n]
    trivial
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, ?_⟩
  rw [← wordLoop_class n w] at hw
  exact Quotient.exact hw.symm

end WordSol


theorem solution (n : ℕ) : EveryLoopHasBraidWord n :=
  WordSol.every_loop n

#print axioms solution
