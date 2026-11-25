-- Prove2me | solution 1 for PI.WickFormula.b_mul_ordEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:43:56.040411+00:00
-- url     : https://prove2.me/submissions/14a7b5b1-5123-467f-b392-4f1e37ecab7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
import Theorems.Thm_PI_WickFormula_lprod_comm
import Theorems.Thm_PI_WickFormula_omon_lower
import Theorems.Thm_PI_WickFormula_ordEval_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
namespace PI.WickFormula
theorem _root_.solution {k AA M : Type} [CommRing k] [Ring AA] [Algebra k AA] [AddCommGroup M] [Module AA M]
    {r s : ℕ} {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}
    (H : Hyp a b a' b' κ σ₀) (i : Fin r) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    b i * ordEval (a + b) (a' + b') R =
      ordEval (a + b) (a' + b') R * b i + ordEval (a + b) (a' + b') (Gen.dL κ i R) := by
  have hcb : ∀ i', Commute (b i) ((a + b) i') := fun i' => by
    simp only [Pi.add_apply]
    exact Commute.add_right (H.h1 i' i).2.1.symm (H.h1 i i').2.2
  have hC : ∀ j j', Commute ((a' + b') j) ((a' + b') j') := fun j j' => by
    simp only [Pi.add_apply]
    exact Commute.add_left (Commute.add_right (H.h2 j j').1 (H.h2 j j').2.1)
      (Commute.add_right (H.h2 j' j).2.1.symm (H.h2 j j').2.2)
  have hbc : ∀ j, b i * (a' + b') j = (a' + b') j * b i + algebraMap k AA (κ i j) := fun j => by
    simp only [Pi.add_apply]
    have h4 := H.h4 i j
    rw [sub_eq_iff_eq_add] at h4
    rw [mul_add, add_mul, (H.h3 i j).eq, h4]
    abel
  have hA : ∀ e : Fin r → ℕ, Commute (b i) (lprod (a + b) e) := fun e => by
    unfold lprod
    apply Commute.list_prod_right
    intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨i', rfl⟩ := hz
    exact (hcb i').pow_right _
  let E : MvPolynomial (Fin r ⊕ Fin s) k →+ AA :=
    AddMonoidHom.mk' (ordEval (a + b) (a' + b')) (ordEval_add _ _)
  induction R using MvPolynomial.induction_on' with
  | monomial m c =>
    have hdl : Gen.dL κ i (monomial m c) =
        ∑ j, κ i j • monomial (m - Finsupp.single (Sum.inr j) 1) (c * (m (Sum.inr j) : k)) := by
      simp [Gen.dL, MvPolynomial.pderiv_monomial]
    have hsum : ordEval (a + b) (a' + b')
        (∑ j, κ i j • monomial (m - Finsupp.single (Sum.inr j) 1) (c * (m (Sum.inr j) : k))) =
        ∑ j, κ i j • ((c * (m (Sum.inr j) : k)) •
          omon (a + b) (a' + b') (m - Finsupp.single (Sum.inr j) 1)) := by
      change E _ = _
      rw [map_sum]
      simp only [E, AddMonoidHom.mk'_apply, ordEval_smul, ordEval_monomial]
    rw [hdl, hsum, ordEval_monomial]
    simp only [omon_lower]
    unfold omon
    rw [mul_smul_comm, ← mul_assoc, (hA _).eq, mul_assoc, lprod_comm (a' + b') hC (b i) (κ i) hbc,
      mul_add, smul_add, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul_comm, smul_smul, smul_smul]
    congr 1
    ring
  | add P Q hP hQ =>
    rw [ordEval_add, mul_add, hP, hQ, map_add, ordEval_add, add_mul]
    abel
end PI.WickFormula
