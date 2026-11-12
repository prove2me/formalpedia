-- Prove2me | solution 1 for Puder.isAlgExt_zpowers_of_mem_crit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:43.004281+00:00
-- url     : https://prove2.me/submissions/de7f3c1e-254a-40db-8321-91e4597f63f5

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg

namespace Puder.Q263C31

variable {d : ℕ} {ι : Type} {J : Subgroup (FreeGroup (Fin d))}

open Classical in
/-- The basis `b` reindexed by `S ⊕ Sᶜ`. -/
noncomputable def B (b : FreeGroupBasis ι J) (S : Set ι) :
    FreeGroupBasis ({i // i ∈ S} ⊕ {i // i ∉ S}) J :=
  b.reindex (Equiv.sumCompl (· ∈ S)).symm

/-- The free group on `S`, mapped into `J` and then into `F_d`. -/
noncomputable def f (b : FreeGroupBasis ι J) (S : Set ι) :
    FreeGroup {i // i ∈ S} →* FreeGroup (Fin d) :=
  J.subtype.comp ((B b S).repr.symm.toMonoidHom.comp (FreeGroup.map Sum.inl))

theorem f_apply (b : FreeGroupBasis ι J) (S : Set ι) (x : FreeGroup {i // i ∈ S}) :
    f b S x = ((B b S).repr.symm (FreeGroup.map Sum.inl x) : FreeGroup (Fin d)) := rfl

theorem f_of (b : FreeGroupBasis ι J) (S : Set ι) (s : {i // i ∈ S}) :
    f b S (FreeGroup.of s) = (b s : FreeGroup (Fin d)) := by
  rw [f_apply, FreeGroup.map.of]
  rfl

theorem f_injective (b : FreeGroupBasis ι J) (S : Set ι) : Function.Injective (f b S) := by
  intro x y h
  rw [f_apply, f_apply] at h
  exact FreeGroup.map_injective Sum.inl_injective
    ((B b S).repr.symm.injective (Subtype.val_injective h))

theorem f_range (b : FreeGroupBasis ι J) (S : Set ι) :
    (f b S).range = Subgroup.closure ((fun i => (b i : FreeGroup (Fin d))) '' S) := by
  rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s.1, s.2, (f_of b S s).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, f_of b S ⟨i, hi⟩⟩

theorem exists_not_mem (b : FreeGroupBasis ι J) (S : Set ι) (h : (f b S).range < J) :
    ∃ i, i ∉ S := by
  by_contra! hS
  apply (lt_iff_le_not_ge.mp h).2
  intro x hx
  have hsurj : Function.Surjective (FreeGroup.map (Sum.inl : {i // i ∈ S} → _ ⊕ {i // i ∉ S})) :=
    FreeGroup.map_surjective (by
      rintro (s | ⟨i, hi⟩)
      · exact ⟨s, rfl⟩
      · exact absurd (hS i) hi)
  obtain ⟨y, hy⟩ := hsurj ((B b S).repr ⟨x, hx⟩)
  refine ⟨y, ?_⟩
  rw [f_apply, hy, MulEquiv.symm_apply_apply]

/-- A basis of the range of `f`, indexed by `S`. -/
noncomputable def e (b : FreeGroupBasis ι J) (S : Set ι) :
    FreeGroup {i // i ∈ S} ≃* (f b S).range :=
  MonoidHom.ofInjective (f_injective b S)

theorem not_prim (b : FreeGroupBasis ι J) (S : Set ι) (w : FreeGroup (Fin d))
    (hw : ¬ IsPrimitiveIn J w) : ¬ IsPrimitiveIn (f b S).range w := by
  rintro ⟨κ, c, k, hk⟩
  apply hw
  let α : FreeGroup {i // i ∈ S} ≃* FreeGroup κ := (e b S).trans c.repr
  let T := {i // i ∈ S}
  let U := {i // i ∉ S}
  let φ : FreeGroup (T ⊕ U) →* FreeGroup (κ ⊕ U) :=
    FreeGroup.lift (Sum.elim (fun s => FreeGroup.map Sum.inl (α (FreeGroup.of s)))
      (fun u => FreeGroup.of (Sum.inr u)))
  let ψ : FreeGroup (κ ⊕ U) →* FreeGroup (T ⊕ U) :=
    FreeGroup.lift (Sum.elim (fun k => FreeGroup.map Sum.inl (α.symm (FreeGroup.of k)))
      (fun u => FreeGroup.of (Sum.inr u)))
  have hψ : ψ.comp (FreeGroup.map Sum.inl) = (FreeGroup.map Sum.inl).comp α.symm.toMonoidHom := by
    apply FreeGroup.ext_hom; intro k; simp [ψ]
  have hφ : φ.comp (FreeGroup.map Sum.inl) = (FreeGroup.map Sum.inl).comp α.toMonoidHom := by
    apply FreeGroup.ext_hom; intro k; simp [φ]
  have h1 : ψ.comp φ = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    rintro (s | u)
    · have := DFunLike.congr_fun hψ (α (FreeGroup.of s))
      simpa [φ] using this
    · simp [φ, ψ]
  have h2 : φ.comp ψ = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    rintro (k | u)
    · have := DFunLike.congr_fun hφ (α.symm (FreeGroup.of k))
      simpa [ψ] using this
    · simp [φ, ψ]
  let Φ : FreeGroup (T ⊕ U) ≃* FreeGroup (κ ⊕ U) :=
    { φ with
      invFun := ψ
      left_inv := fun x => DFunLike.congr_fun h1 x
      right_inv := fun x => DFunLike.congr_fun h2 x }
  refine ⟨κ ⊕ U, FreeGroupBasis.ofRepr ((B b S).repr.trans Φ), Sum.inl k, ?_⟩
  change (((B b S).repr.symm (ψ (FreeGroup.of (Sum.inl k)))) : FreeGroup (Fin d)) = w
  have h3 : ψ (FreeGroup.of (Sum.inl k)) = FreeGroup.map Sum.inl (α.symm (FreeGroup.of k)) := by
    simp [ψ]
  rw [h3, ← f_apply]
  have h4 : (f b S) (α.symm (FreeGroup.of k)) = ((e b S) (α.symm (FreeGroup.of k)) : _) :=
    (MonoidHom.ofInjective_apply (f_injective b S)).symm
  rw [h4, ← hk]
  congr 1
  simp only [α, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply]
  rfl

end Puder.Q263C31

namespace Puder

open Q263C31 in
theorem isAlgExt_zpowers_of_mem_crit_dev {d : ℕ} {w : FreeGroup (Fin d)} {J : Subgroup (FreeGroup (Fin d))}
    (hJ : J ∈ Crit w) : IsAlgExt (Subgroup.zpowers w) J := by
  obtain ⟨hwJ, hnp, r, ⟨bJ⟩, hr⟩ := hJ
  refine ⟨(Subgroup.zpowers_le).mpr hwJ, ?_⟩
  rintro L hwL hLJ ⟨ι, b, S, rfl⟩
  have hι : ι ≃ Fin r := Equiv.ofFreeGroupEquiv (b.repr.symm.trans bJ.repr)
  have : Finite ι := Finite.of_equiv _ hι.symm
  rw [← f_range] at hwL hLJ
  obtain ⟨i, hi⟩ := exists_not_mem b S hLJ
  have hcard : Nat.card {i // i ∈ S} < r := by
    have := Finite.card_subtype_lt (p := (· ∈ S)) hi
    rwa [Nat.card_congr hι, Nat.card_fin] at this
  have hrank : HasRank (f b S).range (Nat.card {i // i ∈ S}) :=
    ⟨(FreeGroupBasis.ofRepr (e b S).symm).reindex (Finite.equivFin _)⟩
  have hle : primitivityRank w ≤ (Nat.card {i // i ∈ S} : ℕ∞) :=
    iInf_le_of_le _ (iInf_le _ ⟨_, (Subgroup.zpowers_le).mp hwL, hrank, not_prim b S w hnp⟩)
  rw [← hr] at hle
  exact absurd (ENat.natCast_le_natCast.mp hle) (not_le.mpr hcard)

end Puder

theorem solution : type_of% @Puder.isAlgExt_zpowers_of_mem_crit_dev := @Puder.isAlgExt_zpowers_of_mem_crit_dev
