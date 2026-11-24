-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThroughTwoPointsTrdeg_proof_bf279ae3b422
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:13.848721+00:00
-- url     : https://prove2.me/submissions/57dc9e38-0413-4084-b2a2-7d07aef99155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughTwoPointsTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ThroughTwoPointsTrdeg
theorem _root_.solution (hT : TrdegAdjoinLe.Statement) : ThroughTwoPointsTrdeg.Statement := by
  intro K Ω _ _ n k _ _ _ hinj x c hcx y j hyj hprop hy
  let u : Fin k × Fin n → Ω := fun im => algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (X im)
  let z : Fin n → Ω := fun m => y m * (y j)⁻¹
  let x' : Fin n → Ω := fun m => algebraMap K Ω (x m)
  let c' : Fin n → Ω := fun m => algebraMap K Ω (c m)
  let s : Fin k → Ω := fun i => ∑ l, u (i, l) * x' l
  have hC : ∀ a : K, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (C a) = algebraMap K Ω a := fun a => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k × Fin n) K) Ω, MvPolynomial.algebraMap_eq]

  have heq : ∀ i, ∑ m, u (i, m) * z m = s i * ∑ m, c' m * z m := by
    intro i
    have h := hy i
    simp only [genSubst, map_sub, map_mul, map_sum, hC] at h
    have h' : ∑ m, u (i, m) * y m = s i * ∑ m, c' m * y m := by
      rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [u, s, x', c']
      ring
    simp only [z, ← mul_assoc, ← Finset.sum_mul]
    rw [h']

  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcx
  have hx'p : x' p ≠ 0 := by simpa [x'] using hp
  obtain ⟨q, hD⟩ : ∃ q, x' p * z q - x' q * z p ≠ 0 := by
    by_contra h
    push Not at h
    apply hprop (y j * (z p * (x' p)⁻¹))
    funext m
    have hm := h m
    simp only [z, x'] at hm hx'p ⊢
    have hm2 : (algebraMap K Ω (x p) * y m - algebraMap K Ω (x m) * y p) * (y j)⁻¹ = 0 := by
      rw [← hm]; ring
    have hm3 := (mul_eq_zero.1 hm2).resolve_right (inv_ne_zero hyj)
    have e : y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        y p * algebraMap K Ω (x m) * (algebraMap K Ω (x p))⁻¹ := by
      rw [show y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        (y j * (y j)⁻¹) * (y p * algebraMap K Ω (x m)) * (algebraMap K Ω (x p))⁻¹ by ring,
        mul_inv_cancel₀ hyj, one_mul]
    rw [e, eq_mul_inv_iff_mul_eq₀ hx'p]
    linear_combination hm3
  set D := x' p * z q - x' q * z p with hDdef
  have hqp : q ≠ p := by
    rintro rfl
    exact hD (by simp [D])
  let E := (Finset.univ.erase p).erase q
  have hqE : q ∈ Finset.univ.erase p := Finset.mem_erase.2 ⟨hqp, Finset.mem_univ q⟩
  have hsplit : ∀ g : Fin n → Ω, ∑ m, g m = g p + g q + ∑ m ∈ E, g m := fun g => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hqE, add_assoc]

  let t : Fin k ⊕ (Fin k × E) → Ω := fun a => Sum.elim s (fun b => u (b.1, b.2.1)) a
  let B := Algebra.adjoin K (Set.range z ∪ Set.range t)
  have hzB : ∀ m, z m ∈ B := fun m => Algebra.subset_adjoin (Or.inl ⟨m, rfl⟩)
  have hsB : ∀ i, s i ∈ B := fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)
  have huB : ∀ i, ∀ m ∈ E, u (i, m) ∈ B := fun i m hm =>
    Algebra.subset_adjoin (Or.inr ⟨Sum.inr (i, ⟨m, hm⟩), rfl⟩)
  have hKB : ∀ a : K, algebraMap K Ω a ∈ B := fun a => B.algebraMap_mem a
  have hczB : ∑ m, c' m * z m ∈ B := B.sum_mem fun m _ => B.mul_mem (hKB _) (hzB m)
  have hDB : D ∈ B := B.sub_mem (B.mul_mem (hKB _) (hzB q)) (B.mul_mem (hKB _) (hzB p))
  have halg : ∀ v, D * v ∈ B → IsAlgebraic B v := fun v hv =>
    IsAlgebraic.of_mul (y := D) (mem_nonZeroDivisors_of_ne_zero hD)
      (isAlgebraic_algebraMap (⟨D, hDB⟩ : B)) (isAlgebraic_algebraMap (⟨D * v, hv⟩ : B))
  have hw : ∀ im, IsAlgebraic B (u im) := by
    rintro ⟨i, m⟩
    have hSx : ∑ m ∈ E, u (i, m) * x' m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hKB _)
    have hSz : ∑ m ∈ E, u (i, m) * z m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hzB m)
    have e1 := hsplit (fun m => u (i, m) * x' m)
    have e2 := hsplit (fun m => u (i, m) * z m)
    rw [heq i] at e2
    change s i = _ at e1
    by_cases hmp : m = p
    · subst hmp
      refine halg _ ?_
      have : D * u (i, m) = z q * (s i - ∑ m ∈ E, u (i, m) * x' m) -
          x' q * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) := by
        rw [hDdef]; linear_combination -z q * e1 + x' q * e2
      rw [this]
      exact B.sub_mem (B.mul_mem (hzB q) (B.sub_mem (hsB i) hSx))
        (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
    by_cases hmq : m = q
    · subst hmq
      refine halg _ ?_
      have : D * u (i, m) = x' p * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) -
          z p * (s i - ∑ m ∈ E, u (i, m) * x' m) := by
        rw [hDdef]; linear_combination -x' p * e2 + z p * e1
      rw [this]
      exact B.sub_mem (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
        (B.mul_mem (hzB p) (B.sub_mem (hsB i) hSx))
    exact isAlgebraic_algebraMap
      (⟨u (i, m), huB i m (Finset.mem_erase.2 ⟨hmq, Finset.mem_erase.2 ⟨hmp, Finset.mem_univ m⟩⟩)⟩ : B)
  have hle := hT K Ω (Set.range z) (Fin k ⊕ (Fin k × E)) t (Fin k × Fin n) u hw

  have hadj : Algebra.adjoin K (Set.range u) = (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω).range := by
    rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hinj' : Function.Injective (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω) := hinj
  have htr : Algebra.trdeg K (Algebra.adjoin K (Set.range u)) = ((k * n : ℕ) : Cardinal) := by
    rw [hadj, ← (AlgEquiv.ofInjective _ hinj').trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have hcard : Fintype.card (Fin k ⊕ (Fin k × E)) = k + k * (n - 2) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Finset.card_erase_of_mem hqE, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [htr, hcard] at hle
  have hn : 2 ≤ n := by
    have := Fin.val_ne_of_ne hqp
    omega
  rcases lt_or_ge (Algebra.trdeg K (Algebra.adjoin K (Set.range z))) Cardinal.aleph0 with hfin | hinf
  · obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
    rw [hd] at hle ⊢
    norm_cast at hle ⊢
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left] at hle
    nlinarith
  · exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans hinf
end ThroughTwoPointsTrdeg
end GroundTheory.Heights₂.Heights
