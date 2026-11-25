-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.cauchyBinet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:39.46675+00:00
-- url     : https://prove2.me/submissions/a87bfa4a-0033-4990-b3a7-b0b3b16d5229

import Mathlib
import Definitions.Def_Lemmata_GeneralBFact_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CauchyBinet
import Theorems.Thm_Bl_general_b_fact_goal1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix MeasureTheory
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS
private lemma cauchyBinet_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  first | exact Bl.general_b_fact.goal1 .. | (apply Bl.general_b_fact.goal1 <;> assumption) | (intros; apply Bl.general_b_fact.goal1 <;> assumption)
private lemma cauchyBinetPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cauchyBinetPar ⟨⟨S, hS⟩, σ⟩) = S := by
  ext x
  simp only [cauchyBinetPar, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem S hS _
  · intro hx
    have : x ∈ Set.range (S.orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨b, rfl⟩ := this
    exact ⟨σ.symm b, by simp⟩
private lemma cauchyBinetPar_bij {i N : ℕ} : Function.Bijective (cauchyBinetPar (i := i) (N := N)) := by
  constructor
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨T, hT⟩, τ⟩ h
    have hST : S = T := by
      rw [← cauchyBinetPar_image S hS σ, ← cauchyBinetPar_image T hT τ, h]
    subst hST
    have : σ = τ := by
      ext a
      have h2 := DFunLike.congr_fun h a
      simp only [cauchyBinetPar, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        RelEmbedding.coe_toEmbedding] at h2
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst this
    rfl
  · intro f
    have hS : (univ.map f).card = i := by simp
    have hmem : ∀ a, f a ∈ Set.range ((univ.map f).orderEmbOfFin hS) := by
      intro a
      rw [Finset.range_orderEmbOfFin]; simp
    choose τ hτ using hmem
    have hinj : Function.Injective τ := by
      intro a b hab
      apply f.injective
      rw [← hτ a, ← hτ b, hab]
    refine ⟨⟨⟨univ.map f, hS⟩, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)⟩, ?_⟩
    ext a
    simp [cauchyBinetPar, hτ]
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix MeasureTheory
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {m i : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin i) (Fin m) R)
    (B : Matrix (Fin m) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin m) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  rw [cauchyBinet_det_mul_fun]
  set F : (Fin i → Fin m) → R := fun f => (∏ a, A a (f a)) * (B.submatrix f id).det with hF
  have h1 : ∑ f : Fin i → Fin m, F f = ∑ f : Fin i ↪ Fin m, F f := by
    have h0 : ∀ f : Fin i → Fin m, ¬ Function.Injective f → F f = 0 := by
      intro f hf
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨a, b, hab, hne⟩ := hf
      have : (B.submatrix f id).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by funext c; simp [Matrix.submatrix_apply, hab])
      simp [hF, this]
    rw [← Finset.sum_filter_of_ne (p := Function.Injective) (s := univ) (f := F)
      (fun f _ hne => by by_contra hc; exact hne (h0 f hc))]
    symm
    apply Finset.sum_bij (fun (f : Fin i ↪ Fin m) _ => (f : Fin i → Fin m))
    · intro f _; simp [f.injective]
    · intro f _ g _ h; exact DFunLike.coe_injective h
    · intro f hf
      exact ⟨⟨f, (Finset.mem_filter.mp hf).2⟩, Finset.mem_univ _, rfl⟩
    · intro f _; rfl
  rw [h1, ← Function.Bijective.sum_comp cauchyBinetPar_bij (fun f => F f), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  rintro ⟨S, hS⟩ _
  set e := S.orderEmbOfFin hS with he
  have h2 : ∀ σ : Equiv.Perm (Fin i), F (cauchyBinetPar ⟨⟨S, hS⟩, σ⟩) =
      (Equiv.Perm.sign σ : R) * (∏ a, A a (e (σ a))) * (B.submatrix e id).det := by
    intro σ
    have h3 : (B.submatrix (fun a => e (σ a)) id).det =
        (Equiv.Perm.sign σ : R) * (B.submatrix e id).det := by
      have := Matrix.det_permute σ (B.submatrix e id)
      rw [← this]; rfl
    show (∏ a, A a (e (σ a))) * (B.submatrix (fun a => e (σ a)) id).det = _
    rw [h3]; ring
  simp_rw [h2]
  rw [← Finset.sum_mul]
  congr 1
  rw [Matrix.det_apply', ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin i)))]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.submatrix_apply, id]
  congr 1
  rw [← Equiv.prod_comp σ]
  simp
end ReciprocityTheory.ChartRestriction.DS
