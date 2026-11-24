-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAddFirst_proof_325536bdb97b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:08.972022+00:00
-- url     : https://prove2.me/submissions/bd917187-38fe-47da-aa68-9505f45363f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumAddFirstField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial GroundTheory.Heights₂.Heights.FieldNumbers
universe u
private lemma mixedDiff_eventually_zero {K : Type*} (h : (K → ℤ) → ℤ)
    (hh : ∀ᶠ m in Filter.atTop, h m = 0) {n : ℕ} (bs : Fin n → K → ℤ) :
    ∀ᶠ m in Filter.atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction (List.ofFn bs) with
  | nil => simpa using hh
  | cons b l ih =>
    have hs : Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-b) Filter.tendsto_id
    filter_upwards [ih, hs.eventually ih] with m h1 h2
    simp [List.foldr, diffStep, h1, h2]
private lemma eventualValue_of_eventually_zero {K : Type*} (f : (K → ℤ) → ℤ)
    (hf : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  classical
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨0, hf⟩
  rw [eventualValue, dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]
end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial GroundTheory.Heights₂.Heights.FieldNumbers
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IntNumAddFirst
theorem _root_.solution (h1 : FieldNumbers.IntNumAdd.Statement.{u})
    (h2 : FieldNumbers.IntNumZeroSlot.Statement.{u})
    (h3 : FieldNumbers.HilbDegreeBound.Statement.{u}) : IntNumAddFirst.Statement.{u} := by
  intro F _ K _ _ ι _ n G hG hGh hdim b₁ b₂ L
  have hupd : ∀ b : K → ℤ,
      Matrix.vecCons b L = Function.update (Matrix.vecCons (0 : K → ℤ) L) 0 b := fun b => by
    simp [Matrix.vecCons, Fin.update_cons_zero]
  by_cases hrel : IsRelevant G
  ·
    have hle : relDim G = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) ∨
        relDim G < ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      have hc : ((n + 1 : ℕ) : WithBot (WithTop ℤ)) = (((n + 1 : ℕ) : ℤ) : WithTop ℤ) := by
        rfl
      unfold relDim
      generalize ringKrullDim (MRing ι F ⧸ G) = x at hdim ⊢
      induction x using WithBot.recBotCoe with
      | bot => exact Or.inr (WithBot.bot_lt_coe _)
      | coe d =>
        induction d using ENat.recTopCoe with
        | top => exfalso; exact absurd hdim (by simp)
        | coe e =>
          have he : e < n + 2 + Fintype.card K := by
            rw [← WithBot.coe_natCast] at hdim
            exact_mod_cast WithBot.coe_lt_coe.1 hdim
          simp only [WithBot.map_coe]
          rw [hc]
          show ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = _ ∨
            ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < _
          rcases (show (e : ℤ) - Fintype.card K ≤ ((n + 1 : ℕ) : ℤ) by omega).lt_or_eq with h | h
          · exact Or.inr (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 h))
          · exact Or.inl (by rw [h])
    rcases hle with heq | hlt
    · rw [hupd (b₁ + b₂), hupd b₁, hupd b₂]
      exact h1 F K ι G hGh hrel (n + 1) heq (Matrix.vecCons 0 L) 0 b₁ b₂
    · simp only [(h2 F K ι G).2 hGh (n + 1) _ hlt, add_zero]
  · have hz := (h3 F K ι G hGh).2 hrel
    simp only [intNum, eventualValue_of_eventually_zero _ (mixedDiff_eventually_zero _ hz _),
      add_zero]
end IntNumAddFirst
end GroundTheory.Heights₂.Heights.NumbersDVR
