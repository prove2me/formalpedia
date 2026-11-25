-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_proof_97552018069d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:11.066208+00:00
-- url     : https://prove2.me/submissions/453b50eb-daf5-4737-bff5-183c1bb995b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFreeParAlgIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_genPar_algIndep_7c92d0181ec3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_algebraicIndependent_of_trdeg_51e66fc3f49b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep
namespace GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep
theorem _root_.solution : FreeParAlgIndep.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hgen hU hT j₀ hx0 htr
  generalize hz : (fun m => x m * (x j₀)⁻¹) = z at htr ⊢
  have hzm : ∀ m, z m = x m * (x j₀)⁻¹ := fun m => by rw [← hz]
  have hz0 : z j₀ = 1 := by rw [hzm, mul_inv_cancel₀ hx0]
  rw [IntermediateField.algebraicIndependent_adjoin_iff]

  let w : (Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n → L :=
    Sum.elim (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1))))
      (fun j => algebraMap (GenParField k e n) L (genPar k e n (.inr j)))
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin (Algebra.adjoin k (Set.range z)) (Set.range w)) L := by
    set A₀ := Algebra.adjoin k (Set.range z) with hA₀
    set B := Algebra.adjoin A₀ (Set.range w) with hB
    have hzB : ∀ m, z m ∈ B := fun m =>
      Subalgebra.algebraMap_mem B (⟨z m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : A₀)
    have hwB : ∀ i, w i ∈ B := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
    have hkB : ∀ c : k, algebraMap k L c ∈ B := fun c => by
      rw [IsScalarTower.algebraMap_apply k A₀ L]
      exact Subalgebra.algebraMap_mem B _
    have hparB : ∀ p, algebraMap (GenParField k e n) L (genPar k e n p) ∈ B := by
      rintro (⟨i, j⟩ | j)
      · by_cases hj : j = j₀
        · rw [hj]
          have hsum : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
            simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
          have h1 := Finset.add_sum_erase Finset.univ
            (fun j => algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j)
            (Finset.mem_univ j₀)
          simp only [hz0, mul_one] at h1
          rw [hsum, ← eq_neg_iff_add_eq_zero] at h1
          rw [h1]
          refine neg_mem (Subalgebra.sum_mem _ fun j' hj' => Subalgebra.mul_mem _ ?_ (hzB j'))
          exact hwB (.inl (i, ⟨j', Finset.ne_of_mem_erase hj'⟩))
        · exact hwB (.inl (i, ⟨j, hj⟩))
      · exact hwB (.inr j)
    have hmem : ∀ b ∈ B, IsAlgebraic B b := fun b hb => isAlgebraic_algebraMap (⟨b, hb⟩ : B)
    have hx0alg : IsAlgebraic B (x j₀) := by
      have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
        simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
      have h2 : IsAlgebraic B
          (∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j) :=
        hmem _ (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hwB (.inr j)) (hzB j))
      have := h2.inv
      rwa [hs, inv_inv] at this
    have hxalg : ∀ m, IsAlgebraic B (x m) := fun m => by
      have hm : x m = z m * x j₀ := by rw [hzm, inv_mul_cancel_right₀ hx0]
      rw [hm]
      exact (hmem _ (hzB m)).mul hx0alg
    have hpoly : ∀ a : MvPolynomial (Par e n) k, algebraMap (GenParField k e n) L
        (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) a) ∈ B := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C c =>
        rw [← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n),
          ← IsScalarTower.algebraMap_apply k (GenParField k e n) L]
        exact hkB c
      | add a b ha hb =>
        rw [map_add, map_add]
        exact Subalgebra.add_mem _ ha hb
      | mul_X a p ha =>
        rw [map_mul, map_mul]
        exact Subalgebra.mul_mem _ ha (hparB p)
    have hK : ∀ f, IsAlgebraic B (algebraMap (GenParField k e n) L f) := fun f => by
      obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Par e n) k) f
      rw [map_div₀, div_eq_mul_inv]
      exact (hmem _ (hpoly a)).mul (hmem _ (hpoly b)).inv
    refine ⟨fun y => ?_⟩
    have hy : y ∈ (MvPolynomial.aeval (R := GenParField k e n) x).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]
      trivial
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
    clear hy
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.aeval_C]
      exact hK c
    | add a b ha hb =>
      rw [map_add]
      exact ha.add hb
    | mul_X a j ha =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact ha.mul (hxalg j)

  have hcard : (e : Cardinal) + #((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n) ≤
      Algebra.trdeg k L := by
    have hind : AlgebraicIndependent k
        (fun p => algebraMap (GenParField k e n) L (genPar k e n p)) :=
      (genPar_algIndep k e n).map' (f := IsScalarTower.toAlgHom k (GenParField k e n) L)
        (algebraMap (GenParField k e n) L).injective
    have hinj : Function.Injective (Sum.elim (fun i : Fin e => (Sum.inl (i, j₀) : Par e n))
        (Sum.elim (fun p : Fin e × {j : Fin n // j ≠ j₀} => (Sum.inl (p.1, p.2.1) : Par e n))
          Sum.inr)) := by
      rintro (i | ⟨i, j, hj⟩ | j) (i' | ⟨i', j', hj'⟩ | j') h <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
          reduceCtorEq, Subtype.mk.injEq, and_true] at h ⊢ <;>
        first | exact h | exact absurd h.2.symm hj' | exact absurd h.2 hj
    calc (e : Cardinal) + #((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n)
        = #(Fin e ⊕ ((Fin e × {j : Fin n // j ≠ j₀}) ⊕ Fin n)) := by simp
      _ ≤ #(Par e n) := Cardinal.mk_le_of_injective hinj
      _ ≤ Algebra.trdeg k L := hind.cardinalMk_le_trdeg
  exact (algebraicIndependent_of_trdeg (Algebra.adjoin k (Set.range z)) w htr hcard).comp
    Sum.inl Sum.inl_injective
end GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep
