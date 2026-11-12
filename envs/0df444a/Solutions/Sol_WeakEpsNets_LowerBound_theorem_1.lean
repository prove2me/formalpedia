-- Prove2me | solution 1 for WeakEpsNets.LowerBound.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:10:18.670661+00:00
-- url     : https://prove2.me/submissions/cd8263fb-22ba-4064-88da-855982f2f262

import Mathlib
import Theorems.Thm_WeakEpsNets_LowerBound_theorem_4
import Definitions.Def_WeakEpsNets_LowerBound_Extremal

section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace WeakEpsNets.Dev.T1
open WeakEpsNets.LowerBound

/-- zero padding -/
def pad {D d : ℕ} (h : D ≤ d) : (Fin D → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x i := if hi : i.val < D then x ⟨i.val, hi⟩ else 0
  map_add' x y := by
    ext i; by_cases hi : i.val < D <;> simp [hi]
  map_smul' c x := by
    ext i; by_cases hi : i.val < D <;> simp [hi]

def restr {D d : ℕ} (h : D ≤ d) : (Fin d → ℝ) → (Fin D → ℝ) := fun y j => y (Fin.castLE h j)

lemma restr_pad {D d : ℕ} (h : D ≤ d) (x : Fin D → ℝ) : restr h (pad h x) = x := by
  ext j
  simp [restr, pad]

lemma pad_inj {D d : ℕ} (h : D ≤ d) : Function.Injective (pad h) := by
  intro x y hxy
  have := congrArg (restr h) hxy
  rwa [restr_pad, restr_pad] at this

lemma weakNet_pad {D d : ℕ} (h : D ≤ d) [DecidableEq (Fin D → ℝ)] [DecidableEq (Fin d → ℝ)]
    (P : Finset (Fin D → ℝ)) (r : ℝ) (X : Finset (Fin d → ℝ))
    (hX : IsWeakNet (P.image (pad h)) r X) : IsWeakNet P r (X.image (restr h)) := by
  classical
  intro C hC hcard
  have hC' : Convex ℝ (pad h '' C) := hC.linear_image (pad h)
  have hP : (P.image (pad h)).card = P.card := Finset.card_image_of_injective _ (pad_inj h)
  have hF : ((P.image (pad h)).filter (fun p => p ∈ pad h '' C)).card
      = (P.filter (fun p => p ∈ C)).card := by
    have : (P.image (pad h)).filter (fun p => p ∈ pad h '' C) = (P.filter (fun p => p ∈ C)).image (pad h) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, z, hz, hzx⟩
        have := pad_inj h hzx
        subst this
        exact ⟨z, ⟨hx, hz⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, x, hy, rfl⟩
    rw [this]; exact Finset.card_image_of_injective _ (pad_inj h)
  obtain ⟨x, hx, z, hz, rfl⟩ := hX (pad h '' C) hC' (by rw [hP, hF]; exact hcard)
  exact ⟨restr h (pad h z), Finset.mem_image_of_mem _ hx, by rw [restr_pad]; exact hz⟩

end WeakEpsNets.Dev.T1

namespace WeakEpsNets.LowerBound
open WeakEpsNets.Dev.T1
open scoped ENNReal

theorem chk_theorem_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ r_d : ℝ, 0 < r_d ∧ ∃ c_d : ℝ, 0 < c_d ∧
      ∀ r : ℝ, r_d ≤ r →
        (∃ P : Finset (Fin d → ℝ), P.Nonempty ∧
          ∀ X : Finset (Fin d → ℝ), IsWeakNet P r X →
            c_d * Real.rpow r (gamma d) ≤ (X.card : ℝ)) ∧
        ENNReal.ofReal (c_d * Real.rpow r (gamma d)) ≤ (f d r : ℝ≥0∞) := by
  classical
  set M : ℤ := ⌊(Real.sqrt (8 * (d : ℝ) + 25) - 1) / 2⌋ with hM
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq0 : 0 ≤ 8 * (d : ℝ) + 25 := by positivity
  have hsq : Real.sqrt (8 * (d : ℝ) + 25) ^ 2 = 8 * (d : ℝ) + 25 := Real.sq_sqrt hsq0
  have h7 : (7 : ℝ) ≤ Real.sqrt (8 * (d : ℝ) + 25) := by
    apply Real.le_sqrt_of_sq_le; linarith
  have hM3 : 3 ≤ M := by
    rw [hM]; apply Int.le_floor.2; push_cast; linarith
  obtain ⟨s, hsM⟩ : ∃ s : ℕ, M = (s : ℤ) + 2 := ⟨(M - 2).toNat, by omega⟩
  have hs : 1 ≤ s := by omega
  have hMle : (M : ℝ) ≤ (Real.sqrt (8 * (d : ℝ) + 25) - 1) / 2 := Int.floor_le _
  have hMR : (M : ℝ) = (s : ℝ) + 2 := by rw [hsM]; push_cast; ring
  have hgam : gamma d = ((s : ℝ) + 2) / 2 := by
    unfold gamma; rw [← hM, hMR]; ring
  have hD : liftDimension s ≤ d := by
    have h1 : (2 * (s : ℝ) + 5) ≤ Real.sqrt (8 * (d : ℝ) + 25) := by linarith
    have h2 : (2 * (s : ℝ) + 5) ^ 2 ≤ 8 * (d : ℝ) + 25 := by
      rw [← hsq]; exact pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (s : ℝ) ^ 2 + 5 * s ≤ 2 * d := by nlinarith
    have h4 : s ^ 2 + 5 * s ≤ 2 * d := by exact_mod_cast h3
    unfold liftDimension; omega
  obtain ⟨rs, hrs, cs, hcs, H⟩ := theorem_4 s hs
  refine ⟨rs, hrs, cs, hcs, fun r hr => ?_⟩
  obtain ⟨P, hPne, hP⟩ := H r hr
  have key : ∀ X : Finset (Fin d → ℝ), IsWeakNet (P.image (pad hD)) r X →
      cs * Real.rpow r (((s : ℝ) + 2) / 2) ≤ (X.card : ℝ) := by
    intro X hX
    have := hP _ (weakNet_pad hD P r X hX)
    exact this.trans (by exact_mod_cast Finset.card_image_le)
  rw [hgam]
  refine ⟨⟨P.image (pad hD), hPne.image _, key⟩, ?_⟩
  have hnn : 0 ≤ cs * Real.rpow r (((s : ℝ) + 2) / 2) :=
    mul_nonneg hcs.le (Real.rpow_nonneg (by linarith) _)
  have hf : weakNetNumber (P.image (pad hD)) r ≤ f d r :=
    le_iSup (fun P : {P : Finset (Fin d → ℝ) // P.Nonempty} => weakNetNumber P.val r)
      ⟨P.image (pad hD), hPne.image _⟩
  refine le_trans ?_ (ENat.toENNReal_le.2 hf)
  by_cases hS : {n : ℕ∞ | ∃ X : Finset (Fin d → ℝ), (X.card : ℕ∞) = n ∧
      IsWeakNet (P.image (pad hD)) r X} = ∅
  · unfold weakNetNumber
    rw [hS, sInf_empty]; simp
  · obtain ⟨n0, hn0⟩ := Set.nonempty_iff_ne_empty.2 hS
    have hmem := csInf_mem (Set.nonempty_of_mem hn0)
    obtain ⟨X, hXc, hXn⟩ := hmem
    unfold weakNetNumber
    rw [← hXc]
    simp only [ENat.toENNReal_coe]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (key X hXn)

end WeakEpsNets.LowerBound
end

theorem solution : type_of% @WeakEpsNets.LowerBound.chk_theorem_1 := @WeakEpsNets.LowerBound.chk_theorem_1
