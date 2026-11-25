-- Prove2me | solution 1 for PI.IsoFunVW.det_mul_eq_sum_oe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:38.25222+00:00
-- url     : https://prove2.me/submissions/06267511-8d69-4c7b-8bfc-7e1e9d842dcb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Theorems.Thm_PI_IsoFunVW_det_mul_eq_sum_fun
import Theorems.Thm_PI_IsoFunVW_det_submatrix_noninj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
open PI PI.IsoFunVW
namespace PI.IsoFunVW
theorem _root_.solution {R : Type*} [CommRing R] {m n : ℕ} [Fintype (Fin m ↪o Fin n)]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det := by
  classical
  rw [det_mul_eq_sum_fun]
  set g : (Fin m → Fin n) → R := fun f => (∏ i, A i (f i)) * (B.submatrix f id).det with hg
  have h1 : ∑ f : Fin m → Fin n, g f =
      ∑ f ∈ univ.filter (fun f : Fin m → Fin n => Function.Injective f), g f := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    split_ifs with hf
    · rfl
    · simp [hg, det_submatrix_noninj B f hf]
  have h2 : ∀ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Perm (Fin m), g (fun i => J (σ i)) := by
    intro J
    rw [← det_transpose (A.submatrix id J), det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have hB : (B.submatrix (fun i => J (σ i)) id) = (B.submatrix J id).submatrix σ id := by
      ext i j; rfl
    simp only [hg, hB, det_permute]
    simp only [transpose_apply, submatrix_apply, id]
    ring
  rw [h1]
  simp_rw [h2]
  rw [← Fintype.sum_prod_type' (fun (J : Fin m ↪o Fin n) (σ : Perm (Fin m)) => g (fun i => J (σ i)))]
  symm
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact p.1.injective.comp p.2.injective
  · intro p _ q _ h
    have hr : Set.range (p.1 : Fin m → Fin n) = Set.range (q.1 : Fin m → Fin n) := by
      have e1 : Set.range (fun i => p.1 (p.2 i)) = Set.range (p.1 : Fin m → Fin n) :=
        p.2.surjective.range_comp _
      have e2 : Set.range (fun i => q.1 (q.2 i)) = Set.range (q.1 : Fin m → Fin n) :=
        q.2.surjective.range_comp _
      rw [← e1, ← e2, h]
    have hJ : p.1 = q.1 :=
      RelEmbedding.ext (congrFun ((p.1.strictMono.range_inj q.1.strictMono).1 hr))
    have hσ : p.2 = q.2 := by
      ext i
      have := congrFun h i
      rw [hJ] at this
      exact congrArg Fin.val (q.1.injective this)
    exact Prod.ext hJ hσ
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    have hs : (univ.image f).card = m := by
      rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
    set J := (univ.image f).orderEmbOfFin hs
    have hmem : ∀ i, ∃ k, J k = f i := by
      intro i
      have : f i ∈ Set.range J := by
        rw [Finset.range_orderEmbOfFin]; simp
      exact this
    choose τ hτ using hmem
    have hτi : Function.Injective τ := by
      intro a b hab
      apply hf
      rw [← hτ a, ← hτ b, hab]
    refine ⟨(J, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτi)), mem_univ _, ?_⟩
    funext i
    simp [hτ]
  · intro p _
    rfl
end PI.IsoFunVW
