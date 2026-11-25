-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_filtration_e7e80f1f0240
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:40.146365+00:00
-- url     : https://prove2.me/submissions/313715a6-2673-4fc3-89c5-d5d80ecdfc1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_colon_isPrime_e41b03fc9ee7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_sup_span_d4fd7e1016c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_eq_zero_89948f02be2c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_self_40c08fc02462
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_colon_add_69a0d85a0ac3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_hilbFn_top_eaf1d44ba056

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
open Classical
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution (h1 : HilbExactDivide.Statement.{u}) (J : Ideal (MRing ι F))
    (hJ : IsMultiHomogIdeal J) :
    ∃ (r : ℕ) (Q : Fin r → Ideal (MRing ι F)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ J ≤ Q j) ∧
      (∀ m, hilbFn J m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ W (hW : W ∈ J.minimalPrimes),
        haveI : W.IsPrime := hW.1.1
        (((∑ j, if Q j = W then 1 else 0 : ℕ)) : ℕ∞) = multAt J W) := by
  induction J using IsNoetherian.induction with
  | hgt J IH =>
  by_cases hJt : J = ⊤
  · subst hJt
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun m => ?_, fun W hW => ?_⟩
    · simp [hilbFn_top]
    · exact absurd (top_le_iff.mp hW.1.2) hW.1.1.ne_top
  obtain ⟨c, s, hs, hsJ, hQp, hQh⟩ := exists_colon_isPrime hJ hJt
  have hJQ : J ≤ J.colon (Ideal.span {s}) := fun x hx =>
    mem_colon_iff.mpr (Ideal.mul_mem_right s J hx)
  have hgt : J < J ⊔ Ideal.span {s} :=
    lt_of_le_of_ne le_sup_left (fun h => hsJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self s)))
  obtain ⟨r, Q', c', hQ', hh', hcount'⟩ := IH _ hgt (multiHomog_sup_span hJ hs)
  refine ⟨r + 1, Fin.cons (J.colon (Ideal.span {s})) Q', Fin.cons c c', ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]
      exact ⟨hQp, hQh, hJQ⟩
    · simp only [Fin.cons_succ]
      exact ⟨(hQ' j).1, (hQ' j).2.1, le_sup_left.trans (hQ' j).2.2⟩
  · intro m
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hh' m]
    have := h1 F K ι J hJ c s hs m
    linarith
  · intro W hW
    have : W.IsPrime := hW.1.1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [multAt_colon_add J W s, Nat.cast_add]
    congr 1
    · by_cases hle : J.colon (Ideal.span {s}) ≤ W
      · have heq : J.colon (Ideal.span {s}) = W := le_antisymm hle (hW.2 ⟨hQp, hJQ⟩ hle)
        rw [if_pos heq]
        simp only [heq]
        rw [multAt_self]
        rfl
      · rw [if_neg (fun h => hle h.le), multAt_eq_zero hle]
        rfl
    · by_cases hJ'W : J ⊔ Ideal.span {s} ≤ W
      · have hW' : W ∈ Ideal.minimalPrimes (J ⊔ Ideal.span {s}) :=
          ⟨⟨hW.1.1, hJ'W⟩, fun q hq hqW => hW.2 ⟨hq.1, le_sup_left.trans hq.2⟩ hqW⟩
        exact hcount' W hW'
      · rw [multAt_eq_zero hJ'W]
        have : ∀ j, Q' j ≠ W := fun j h => hJ'W (h ▸ (hQ' j).2.2)
        simp [this]
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
