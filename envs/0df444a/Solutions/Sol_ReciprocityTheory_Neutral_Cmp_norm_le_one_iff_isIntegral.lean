-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.norm_le_one_iff_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:28.721884+00:00
-- url     : https://prove2.me/submissions/332ab2b0-a3a8-4354-822f-cb61d50857a7

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (x : PadicAlgCl p) : ‖x‖ ≤ 1 ↔ IsIntegral (PadicInt.subring p) x := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm := minpoly.monic hint
  change spectralValue (minpoly ℚ_[p] x) ≤ 1 ↔ _
  rw [spectralValue_le_one_iff hm]
  constructor
  · intro hc
    have hl : minpoly ℚ_[p] x ∈ Polynomial.lifts (PadicInt.subring p).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    have e : algebraMap (PadicInt.subring p) (PadicAlgCl p) =
        (algebraMap ℚ_[p] (PadicAlgCl p)).comp (PadicInt.subring p).subtype := rfl
    rw [e, ← Polynomial.eval₂_map, hq]
    exact minpoly.aeval ℚ_[p] x
  · rintro ⟨q, hqm, he⟩
    set P := q.map (PadicInt.subring p).subtype
    have hPm : P.Monic := hqm.map _
    have hP : Polynomial.aeval x P = 0 := by
      have e : algebraMap (PadicInt.subring p) (PadicAlgCl p) =
          (algebraMap ℚ_[p] (PadicAlgCl p)).comp (PadicInt.subring p).subtype := rfl
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← e]
      exact he
    have h1 : spectralNorm ℚ_[p] (PadicAlgCl p) x ≤ spectralValue P :=
      norm_root_le_spectralValue (f := spectralAlgNorm ℚ_[p] (PadicAlgCl p))
        spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm hPm hP
    have h2 : spectralValue P ≤ 1 := by
      rw [spectralValue_le_one_iff hPm]
      intro n
      rw [Polynomial.coeff_map]
      exact (q.coeff n).2
    have h3 : spectralValue (minpoly ℚ_[p] x) ≤ 1 := h1.trans h2
    exact (spectralValue_le_one_iff hm).1 h3
end ReciprocityTheory.Neutral.Cmp
