-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:25.477774+00:00
-- url     : https://prove2.me/submissions/f44c60fa-4066-4d0c-b246-e66bcbe3d9f4

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
private lemma det_sum_eq_pi (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (S : Finset (Fin D)) :
    (∑ k ∈ S, A k).det = ∑ f ∈ Fintype.piFinset (fun _ : Fin D => S),
      (Matrix.of fun i j => A (f j) i j).det := by
  classical
  rw [← Matrix.det_transpose]
  have h : (∑ k ∈ S, A k)ᵀ = fun j => ∑ k ∈ S, (fun i => A k i j) := by
    ext j i; simp [Matrix.sum_apply, Finset.sum_apply]
  rw [h]
  have := (Matrix.detRowAlternating (R := ℂ) (n := Fin D)).toMultilinearMap.map_sum_finset
    (fun j k => fun i => A k i j) (fun _ => S)
  simp only [AlternatingMap.coe_multilinearMap] at this
  show Matrix.detRowAlternating _ = _
  rw [this]
  exact Finset.sum_congr rfl fun f _ => (Matrix.det_transpose _).symm
private lemma sum_sign_indicator (f : Fin D → Fin D) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) *
      (if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) =
      if Function.Surjective f then 1 else 0 := by
  classical
  set T := Finset.univ.image f with hT
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (compl_involutive (α := Finset (Fin D))))]
  have hc : ∀ U : Finset (Fin D), D - (Uᶜ).card = U.card := by
    intro U
    rw [Finset.card_compl, Fintype.card_fin]
    exact Nat.sub_sub_self (by simpa using Finset.card_le_univ U)
  have hmem : ∀ U : Finset (Fin D),
      f ∈ Fintype.piFinset (fun _ : Fin D => Uᶜ) ↔ U ∈ Tᶜ.powerset := by
    intro U
    simp only [Fintype.mem_piFinset, Finset.mem_compl, Finset.mem_powerset, Finset.subset_iff, hT,
      Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact ⟨fun h x hx a ha => h a (ha ▸ hx), fun h a ha => h ha a rfl⟩
  simp only [Function.Involutive.coe_toPerm, hc, hmem, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hz : (∑ U ∈ Tᶜ.powerset, (-1 : ℂ) ^ U.card) = ((∑ U ∈ Tᶜ.powerset, (-1 : ℤ) ^ U.card : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hz, Finset.sum_powerset_neg_one_pow_card]
  have hs : Tᶜ = ∅ ↔ Function.Surjective f := by
    rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
    simp [hT, Function.Surjective]
  by_cases h : Function.Surjective f
  · simp [hs.2 h, h]
  · rw [if_neg (fun h' => h (hs.1 h')), if_neg h]; simp
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc A = (1 / (D.factorial : ℂ)) *
      ∑ σ : Equiv.Perm (Fin D), (Matrix.of fun i j => A (σ j) i j).det := by
  classical
  unfold mdisc
  congr 1
  set G : (Fin D → Fin D) → ℂ := fun f => (Matrix.of fun i j => A (f j) i j).det with hG
  have key : ∀ S : Finset (Fin D), (∑ k ∈ S, A k).det =
      ∑ f, (if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) * G f := by
    intro S
    rw [det_sum_eq_pi]
    simp only [ite_mul, one_mul, zero_mul, hG]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ f : Fin D → Fin D, ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) *
      ((if f ∈ Fintype.piFinset (fun _ : Fin D => S) then 1 else 0) * G f) =
      (if Function.Surjective f then 1 else 0) * G f := by
    intro f
    rw [← sum_sign_indicator f, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by ring
  simp_rw [h2, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun σ _ => ⇑σ) (fun σ _ => by simpa using σ.surjective)
    (fun a _ b _ h => Equiv.ext (congrFun h)) (fun f hf => ?_) (fun σ _ => rfl)
  have hs : Function.Surjective f := by simpa using hf
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hs, hs⟩, Finset.mem_univ _, rfl⟩
end ReciprocityTheory.AnForm.A
