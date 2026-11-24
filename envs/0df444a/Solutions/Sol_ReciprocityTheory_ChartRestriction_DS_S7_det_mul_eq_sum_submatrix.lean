-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:54.032016+00:00
-- url     : https://prove2.me/submissions/6efcda1d-c9d3-4c34-9af3-fb2cbc4045ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_GeneralBFact_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private lemma cb_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have hrow : A * B = Matrix.of (fun a => ∑ j, A a j • B j) := by
    ext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow]
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a j => A a j • B j)
  have h2 : ∀ f : Fin i → Fin N,
      (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap (fun a => A a (f a) • B (f a)) =
        (∏ a, A a (f a)) * (B.submatrix f id).det := by
    intro f
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  exact h1.trans (Finset.sum_congr rfl fun f _ => h2 f)
private lemma cbPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cbPar ⟨⟨S, hS⟩, σ⟩) = S := by
  simp only [cbPar]
  rw [← Finset.map_map, Finset.map_univ_equiv]
  exact Finset.map_orderEmbOfFin_univ S hS
private lemma cbPar_bij {i N : ℕ} : Function.Bijective (cbPar (i := i) (N := N)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨S', hS'⟩, σ'⟩ h
    have hSS : S = S' := by
      rw [← cbPar_image S hS σ, ← cbPar_image S' hS' σ', h]
    subst hSS
    have hσ : σ = σ' := by
      ext a
      have h2 := DFunLike.congr_fun h a
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst hσ
    rfl
  · intro g
    have hcard : (univ.map g).card = i := by simp
    have hmem : ∀ a, g a ∈ univ.map g := fun a => Finset.mem_map_of_mem g (Finset.mem_univ a)
    let g' : Fin i ≃ (univ.map g) := Equiv.ofBijective (fun a => ⟨g a, hmem a⟩)
      ⟨fun a b h => g.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
        exact ⟨a, rfl⟩⟩
    refine ⟨⟨⟨univ.map g, hcard⟩, g'.trans ((univ.map g).orderIsoOfFin hcard).symm.toEquiv⟩, ?_⟩
    refine DFunLike.ext _ _ fun a => ?_
    change ((univ.map g).orderEmbOfFin hcard) (((univ.map g).orderIsoOfFin hcard).symm (g' a)) = g a
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rfl
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  have hz : ∀ f : Fin i → Fin N, ¬ Function.Injective f →
      (∏ a, A a (f a)) * (B.submatrix f id).det = 0 := by
    intro f hf
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [hab]), mul_zero]
  have hS : ∀ S : {S : Finset (Fin N) // S.card = i},
      ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det =
        (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    intro S
    have hA : (A.submatrix id (S.1.orderEmbOfFin S.2)).det =
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ a, A a (S.1.orderEmbOfFin S.2 (σ a)) := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
    rw [hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hB : B.submatrix (cbPar ⟨S, σ⟩) id = (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id := rfl
    rw [hB, Matrix.det_permute]
    change (∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))) * _ = _
    ring
  calc (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        cb_det_mul_fun A B
    _ = ∑ f ∈ univ.filter Function.Injective, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        (Finset.sum_filter_of_ne fun f _ hf => by
          by_contra hni
          exact hf (hz f hni)).symm
    _ = ∑ x : {f : Fin i → Fin N // Function.Injective f},
          (∏ a, A a (x.1 a)) * (B.submatrix x.1 id).det :=
        Finset.sum_subtype _ (fun f => by simp) _
    _ = ∑ g : Fin i ↪ Fin N, (∏ a, A a (g a)) * (B.submatrix g id).det :=
        Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)
    _ = ∑ p, (∏ a, A a (cbPar p a)) * (B.submatrix (cbPar p) id).det :=
        (cbPar_bij.sum_comp (fun g : Fin i ↪ Fin N => (∏ a, A a (g a)) * (B.submatrix g id).det)).symm
    _ = ∑ S, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det :=
        Fintype.sum_sigma _
    _ = _ := Finset.sum_congr rfl fun S _ => hS S
end ReciprocityTheory.ChartRestriction.DS.S7
