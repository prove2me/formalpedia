-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:52:25.536427+00:00
-- url     : https://prove2.me/submissions/543e7bfd-b73e-45bc-991b-714bf21b56a3

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_val_le_iff_div_mem
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_exists_div_aeval
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_nonunits
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤)
    (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (ϖ : Ω) (hdiv : ∀ y ∈ (V.comap (algebraMap Ω U)).nonunits,
      y / ϖ ∈ V.comap (algebraMap Ω U)) (z : U) (hz : z ∈ V.nonunits) :
    z / algebraMap Ω U ϖ ∈ V := by
  classical
  set W := V.comap (algebraMap Ω U) with hWdef
  by_cases hϖ : ϖ = 0
  · simp [hϖ]
  have hϖ' : algebraMap Ω U ϖ ≠ 0 := by simpa using hϖ
  obtain ⟨p, q, hq, rfl⟩ := gauss_exists_div_aeval t hgen z
  have hP := gauss_val t V ht hind p
  have hQ := gauss_val t V ht hind q
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hqs : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hq0
  obtain ⟨β, hβ, hβeq⟩ := Finset.exists_mem_eq_sup q.support hqs
    (fun α => V.valuation (algebraMap Ω U (q.coeff α)))
  have hqβ : q.coeff β ≠ 0 := MvPolynomial.mem_support_iff.mp hβ
  have hqβ' : algebraMap Ω U (q.coeff β) ≠ 0 := by simpa using hqβ
  have hvQ : V.valuation (aeval t q) = V.valuation (algebraMap Ω U (q.coeff β)) := hQ.trans hβeq
  have hvQpos : (0 : _) < V.valuation (aeval t q) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hq)
  have hzlt : V.valuation (aeval t p) < V.valuation (aeval t q) := by
    have := (V.mem_nonunits_iff).mp hz
    rwa [map_div₀, div_lt_one₀ hvQpos] at this
  rw [← gauss_val_le_iff_div_mem V hϖ', map_div₀, div_le_iff₀ hvQpos]
  rw [hP, Finset.sup_le_iff]
  intro α hα
  have hle : V.valuation (algebraMap Ω U (p.coeff α)) ≤ V.valuation (aeval t p) := by
    rw [hP]; exact Finset.le_sup (f := fun α => V.valuation (algebraMap Ω U (p.coeff α))) hα
  have hnu : algebraMap Ω U (p.coeff α / q.coeff β) ∈ V.nonunits := by
    rw [V.mem_nonunits_iff, map_div₀, map_div₀, ← hvQ, div_lt_one₀ hvQpos]
    exact lt_of_le_of_lt hle hzlt
  have hnuW : p.coeff α / q.coeff β ∈ W.nonunits := (gauss_nonunits V _).mp hnu
  have hdivW := hdiv _ hnuW
  have hmem : algebraMap Ω U (p.coeff α / q.coeff β) / algebraMap Ω U ϖ ∈ V := by
    rw [← map_div₀]; exact hdivW
  have := (gauss_val_le_iff_div_mem V hϖ').mpr hmem
  rw [map_div₀, map_div₀, ← hvQ, div_le_iff₀ hvQpos] at this
  rw [hvQ] at this ⊢
  first
  | exact this
  | exact this.trans_eq (mul_comm _ _)
end ReciprocityTheory.MultiplicativeHeights
