-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_proof_e9bfb864d7e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:49.52182+00:00
-- url     : https://prove2.me/submissions/01494064-0d77-41df-bf41-01be7611498d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mixedDiff_snoc_e7ce994421e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_intNum_eq_zero_of_eventually_fcf290f727c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_top_234e7946562e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_eventually_zero_of_not_relevant_ade284a05af1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_isMultiHomogIdeal_sup_span_9559967f1914
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_colon_eq_of_not_mem_041a78df4446
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_sup_span_add_one_le_6e63ac6fa7da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_ringKrullDim_minimalPrime_fb3bba25115f

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
open CutRegular
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace CutRegular
theorem _root_.solution (h1 : HilbExactDivide.Statement.{u}) (h2 : MultEqualsCoeff.Statement.{u})
    (_h3 : IntNumSymm.Statement.{u}) : CutRegular.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hdim c s hs hsP bs
  haveI := hP.isPrime
  set I := P ⊔ Ideal.span {s} with hIdef
  have hdiff : diffStep (fun k => (c k : ℤ)) (hilbFn P) = hilbFn I := by
    funext m
    have := h1 F K ι P hP.multiHomog c s hs m
    rw [colon_eq_of_not_mem hsP] at this
    exact this
  have hLHS : intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (c k : ℤ))) =
      intNum F I bs := by
    unfold intNum
    rw [mixedDiff_snoc, hdiff]
  rw [hLHS]
  have hP' : ringKrullDim (MRing ι F ⧸ P) = ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    rw [(relDim_eq_natCast_iff P (n + 1)).mp hdim, show n + 1 + Fintype.card K =
      n + Fintype.card K + 1 by omega]
  have hmin : ∀ W ∈ I.minimalPrimes,
      ringKrullDim (MRing ι F ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    fun W hW => ringKrullDim_minimalPrime hsP hW hP'
  by_cases hgood : IsRelevant I ∧ I ≠ ⊤
  · obtain ⟨hrel, hne⟩ := hgood
    have hIdim : relDim I = ((n : ℕ) : WithBot (WithTop ℤ)) := by
      rw [relDim_eq_natCast_iff]
      obtain ⟨⟨W, hW⟩⟩ := Ideal.nonempty_minimalPrimes hne
      have _ : W.IsPrime := hW.1.1
      have hle : ringKrullDim (MRing ι F ⧸ W) ≤ ringKrullDim (MRing ι F ⧸ I) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.1.2)
          (Ideal.Quotient.factor_surjective hW.1.2)
      rw [hmin W hW] at hle
      have hup := ringKrullDim_sup_span_add_one_le hsP
      rw [hP'] at hup
      exact eq_of_add_one_le_of_le hup hle
    rw [h2 F K ι I (isMultiHomogIdeal_sup_span hP.multiHomog hs) hrel n hIdim bs]
    congr 1
    funext W
    unfold topCycle divCycle
    by_cases hW : W ∈ I.minimalPrimes ∧ IsRelevant W
    · have hWd : relDim W = ((n : ℕ) : WithBot (WithTop ℤ)) :=
        (relDim_eq_natCast_iff W n).mpr (hmin W hW.1)
      rw [dif_pos ⟨hW.1, hW.2, hWd⟩, dif_pos hW]
    · rw [dif_neg (fun h => hW ⟨h.1, h.2.1⟩), dif_neg hW]
  · have hzero : ∀ᶠ m in Filter.atTop, hilbFn I m = 0 := by
      by_cases htop : I = ⊤
      · rw [htop]
        exact Filter.Eventually.of_forall hilbFn_top
      · exact hilbFn_eventually_zero_of_not_relevant (fun h => hgood ⟨h, htop⟩)
    rw [intNum_eq_zero_of_eventually hzero]
    have hdiv : divCycle P s = 0 := by
      funext W
      simp only [Pi.zero_apply]
      unfold divCycle
      rw [dif_neg]
      rintro ⟨hWm, hWr⟩
      have hIW : I ≤ W := hWm.1.2
      by_cases htop : I = ⊤
      · exact hWm.1.1.ne_top (top_le_iff.mp (htop ▸ hIW))
      · refine hgood ⟨fun k => ?_, htop⟩
        obtain ⟨i, hi⟩ := hWr k
        exact ⟨i, fun h => hi (hIW h)⟩
    rw [hdiv]
    simp [cycEval]
end CutRegular
end GroundTheory.Heights₂.Heights.FieldNumbers
