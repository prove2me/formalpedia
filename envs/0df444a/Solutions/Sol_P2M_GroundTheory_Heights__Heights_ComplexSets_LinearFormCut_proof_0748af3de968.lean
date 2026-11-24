-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_LinearFormCut_proof_0748af3de968
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:35.393388+00:00
-- url     : https://prove2.me/submissions/2532d2bb-e6ce-4e8b-a5f9-7d1c425f557b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace LinearFormCut
theorem _root_.solution : LinearFormCut.Statement := by
  intro n e I hI
  classical
  let S := {Q : Ideal (MvPolynomial (Fin n) ℂ) | Q ∈ I.minimalPrimes ∧ Q ≠ originIdeal n}
  have : Finite S :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun Q hQ => hQ.1).to_subtype
  let p : S → Submodule ℂ (Fin n → ℂ) := fun Q => (Q.1.restrictScalars ℂ).comap (formMap n)
  have hp : ∀ Q, p Q ≠ ⊤ := by
    intro Q htop
    apply Q.2.2
    have hle : originIdeal n ≤ Q.1 := by
      rw [originIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.single j 1 ∈ p Q := htop ▸ Submodule.mem_top
      simpa [p, formMap, Pi.single_apply] using this
    exact ((originIdeal_isMaximal n).eq_of_le Q.2.1.1.1.ne_top hle).symm
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let B : Matrix (Fin 1) (Fin n) ℂ := Matrix.of fun _ j => a j
  refine ⟨B, ?_⟩
  have hl : formMap n a ∈ linIdeal B := Ideal.subset_span ⟨0, by simp [linPoly, formMap, B]⟩
  rw [ringKrullDim_quotient] at hI ⊢
  refine iSup_le fun l => ?_
  have hIh : I ≤ l.head.1.asIdeal := fun y hy => l.head.2 (Ideal.mem_sup_left hy)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hIh
  by_cases hQo : Q = originIdeal n
  · have hM : l.head.1.asIdeal.IsMaximal := by
      rw [← (originIdeal_isMaximal n).eq_of_le l.head.1.isPrime.ne_top (hQo ▸ hQle)]
      exact originIdeal_isMaximal n
    have h0 : l.length = 0 := by
      by_contra h
      have hlt : l.head < l.last := l.strictMono (Fin.pos_iff_ne_zero.2 (by simp [Fin.ext_iff]; omega))
      have hlt' : l.head.1.asIdeal < l.last.1.asIdeal := hlt
      exact (hM.eq_of_le l.last.1.isPrime.ne_top hlt'.le ▸ hlt').false
    simp [h0]
  · have hQa : formMap n a ∉ Q := ha ⟨Q, hQ, hQo⟩
    let f : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑(I ⊔ linIdeal B) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      fun x => ⟨x.1, fun y hy => x.2 (Ideal.mem_sup_left hy)⟩
    have hf : StrictMono f := fun x y h => h
    let q0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      ⟨⟨Q, hQ.1.1⟩, fun y hy => hQ.1.2 hy⟩
    have hq : q0 < (l.map f hf).head := by
      refine lt_of_le_of_ne hQle fun h => hQa ?_
      have : formMap n a ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right hl)
      have hQh : Q = l.head.1.asIdeal :=
        congrArg (fun x : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I => x.1.asIdeal) h
      rwa [hQh]
    have hlen := (Order.LTSeries.length_le_krullDim ((l.map f hf).cons q0 hq)).trans hI
    simp only [RelSeries.cons_length] at hlen
    have : l.length + 1 ≤ e + 1 := by exact_mod_cast hlen
    exact_mod_cast (by omega : l.length ≤ e)
end LinearFormCut
end GroundTheory.Heights₂.Heights.ComplexSets
