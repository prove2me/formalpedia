-- Prove2me | solution 1 for Rep.exists_resMap_comp_eq_comp_add_iota_comp_of_pit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3e67015d-82f0-5039-9637-a287ecb57986

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit

set_option autoImplicit false
open CategoryTheory

namespace PitCoker

universe u
variable {k : Type u} [CommRing k] {G : Type u} [Group G]

lemma ρ_one_apply {V : Rep.{u} k G} (v : V) : V.ρ 1 v = v := by
  rw [map_one, Module.End.one_apply]

lemma ρ_nsmul {V : Rep.{u} k G} (g : G) (n : ℕ) (v : V) : V.ρ g (n • v) = n • V.ρ g v := map_nsmul _ _ _

def homAdd {V W : Rep.{u} k G} (χ : V ⟶ W) : V →+ W := χ.hom.toLinearMap.toAddMonoidHom

lemma homAdd_apply {V W : Rep.{u} k G} (χ : V ⟶ W) (v : V) : homAdd χ v = χ.hom v := rfl

lemma hom_apply_eq_of_comp_eq {X Y Y' Z : Rep.{u} k G} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z}
    (w : f ≫ g = f' ≫ g') (x : X) : g.hom (f.hom x) = g'.hom (f'.hom x) := by
  have := congrArg (fun φ => Rep.Hom.hom φ x) w
  simpa [Rep.hom_comp] using this

lemma freeLift_hom_single_single_one {α : Type u} {A : Rep.{u} k G} (f : α → A) (i : α) (g : G) :
    (Rep.freeLift k G A f).hom (Finsupp.single i (MonoidAlgebra.single g 1)) = A.ρ g (f i) := by
  change Representation.freeLift A.ρ f (Finsupp.single i (MonoidAlgebra.single g 1)) = _
  rw [Representation.freeLift_single_single, one_smul]

noncomputable def kerCover (B : Rep.{u} k G) : Submodule k (Rep.free k G B) := LinearMap.ker (Rep.freeCover B).hom.toLinearMap

lemma mem_kerCover_iff (B : Rep.{u} k G) (x : Rep.free k G B) : x ∈ kerCover B ↔ (Rep.freeCover B).hom x = 0 := LinearMap.mem_ker

lemma free_ρ_single_single {α : Type u} (g h : G) (i : α) (r : k) :
    (Rep.free k G α).ρ g (Finsupp.single i (MonoidAlgebra.single h r)) = Finsupp.single i (MonoidAlgebra.single (g * h) r) :=
  Representation.free_single_single g h i r

end PitCoker

lemma PitCoker.finsupp₂_addHom_ext {α G M : Type} [AddCommGroup M] (φ ψ : (α →₀ MonoidAlgebra ℤ G) →+ M)
    (h : ∀ (a : α) (g : G), φ (Finsupp.single a (MonoidAlgebra.single g 1)) = ψ (Finsupp.single a (MonoidAlgebra.single g 1))) : φ = ψ := by
  apply Finsupp.addHom_ext'
  intro a
  apply MonoidAlgebra.addHom_ext'
  intro g
  apply AddMonoidHom.ext_int
  simpa using h a g

open PitCoker in
theorem solution
    {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
    (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
    (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
    (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)
    (t : Rep.relationModuleInt B ⟶ T.X₂) :
    ∃ (t' : Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₁) (χ : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₂),
      Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ φ₂ =
        t' ≫ T'.f + Rep.relationModuleInt.ι (Rep.res π B) ≫ χ := by
  classical
  have _ := hT
  have _ := w₁

  let u : Rep.relationModuleInt B ⟶ T.X₃ := t ≫ T.g

  have hp : p.Prime := Fact.out
  let N : ℕ := Nat.card T.X₃
  have hN0 : N ≠ 0 := (Nat.card_pos (α := T.X₃)).ne'
  let a : ℕ := N.factorization p
  let n : ℕ := ordCompl[p] N
  have hpan : p ^ a * n = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime (p ^ (a + 1)) n := (Nat.coprime_ordCompl hp hN0).pow_left _
  obtain ⟨α, β, hαβ⟩ : IsCoprime ((p ^ (a + 1) : ℕ) : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hNc : ∀ c : T.X₃, N • c = 0 := fun c => card_nsmul_eq_zero'

  let F := Rep.free ℤ G B
  have hpF : ∀ x : F, (p • x : F) ∈ kerCover B := by
    intro x
    rw [mem_kerCover_iff]
    change homAdd (Rep.freeCover B) (p • x) = 0
    rw [map_nsmul, homAdd_apply]
    exact hB _
  let pR : F →+ Rep.relationModuleInt B :=
    { toFun := fun x => (show Rep.relationModule B from ⟨p • x, hpF x⟩)
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun x y => Subtype.ext (smul_add _ _ _) }
  have pR_val : ∀ x : F, (Rep.relationModuleInt.ι B).hom (pR x) = p • x := fun x => rfl
  have pR_ρ : ∀ (g : G) (x : F), pR (F.ρ g x) = (Rep.relationModuleInt B).ρ g (pR x) := fun g x =>
    Subtype.ext (by
      change p • F.ρ g x = F.ρ g (p • x)
      rw [ρ_nsmul])
  let w₀ : F ⟶ T.X₃ := Rep.freeLift ℤ G T.X₃ (fun b : B => u.hom (pR (Finsupp.single b (MonoidAlgebra.single 1 1))))
  have hw₀ : ∀ x : F, w₀.hom x = u.hom (pR x) := by
    intro x
    have key : homAdd w₀ = (homAdd u).comp pR := finsupp₂_addHom_ext _ _ (fun b g => by
      rw [AddMonoidHom.comp_apply, homAdd_apply, homAdd_apply, freeLift_hom_single_single_one,
        ← Rep.hom_comm_apply u, ← pR_ρ, free_ρ_single_single, mul_one])
    exact DFunLike.congr_fun key x
  have hw₀ι : ∀ r : Rep.relationModuleInt B, w₀.hom ((Rep.relationModuleInt.ι B).hom r) = p • u.hom r := by
    intro r
    rw [hw₀]
    change homAdd u (pR _) = p • homAdd u r
    rw [← map_nsmul]
    congr 1

  have h1 : (1 : ℤ) = α * p ^ a * p + β * n := by rw [← hαβ]; push_cast; ring
  have dec : ∀ r : Rep.relationModuleInt B,
      u.hom r = (α * p ^ a : ℤ) • w₀.hom ((Rep.relationModuleInt.ι B).hom r) + (β * n : ℤ) • u.hom r := by
    intro r
    rw [hw₀ι, ← natCast_zsmul, ← mul_zsmul, ← add_zsmul, ← h1, one_zsmul]
  have kill : ∀ c : T.X₃, φ₃.hom ((β * n : ℤ) • c) = 0 := by
    intro c
    refine hpit _ ⟨a, ?_⟩
    rw [← natCast_zsmul, ← mul_zsmul, show ((p ^ a : ℕ) : ℤ) * (β * n) = β * (N : ℤ) by rw [← hpan]; push_cast; ring, mul_zsmul,
      natCast_zsmul, hNc, zsmul_zero]

  let W' : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₃ := (α * p ^ a : ℤ) • (Rep.freeResMap π B ≫ (Rep.resFunctor π).map w₀ ≫ φ₃)
  have hW' : ∀ x', W'.hom x' = (α * p ^ a : ℤ) • φ₃.hom (w₀.hom ((Rep.freeResMap π B).hom x')) := fun x' => rfl
  have hg' : Function.Surjective T'.g.hom := (Rep.epi_iff_surjective T'.g).1 hT'.epi_g
  let χ : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₂ :=
    Rep.freeLift ℤ G' T'.X₂ (fun b : Rep.res π B => Function.surjInv hg' (W'.hom (Finsupp.single b (MonoidAlgebra.single 1 1))))
  have hχ : χ ≫ T'.g = W' := by
    apply Rep.free_ext
    intro b
    change T'.g.hom (χ.hom (Finsupp.single b (MonoidAlgebra.single 1 1))) = W'.hom (Finsupp.single b (MonoidAlgebra.single 1 1))
    rw [freeLift_hom_single_single_one, ρ_one_apply]
    exact Function.surjInv_eq hg' _

  let s : Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₂ := Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ φ₂
  have hs : s ≫ T'.g = Rep.relationModuleInt.ι (Rep.res π B) ≫ W' := Rep.hom_ext (DFunLike.ext _ _ fun r' => by
    change T'.g.hom (φ₂.hom (t.hom ((Rep.relationModuleInt.resMap π B).hom r'))) =
      W'.hom ((Rep.relationModuleInt.ι (Rep.res π B)).hom r')
    rw [← hom_apply_eq_of_comp_eq w₂]
    change φ₃.hom (u.hom ((Rep.relationModuleInt.resMap π B).hom r')) = _
    rw [dec, ← homAdd_apply φ₃, map_add, map_zsmul, homAdd_apply, homAdd_apply, kill, add_zero, hW']
    rfl)

  haveI := hT'.mono_f
  have hzero : (s - Rep.relationModuleInt.ι (Rep.res π B) ≫ χ) ≫ T'.g = 0 := by
    rw [Preadditive.sub_comp, hs, Category.assoc, hχ, sub_self]
  refine ⟨hT'.exact.lift _ hzero, χ, ?_⟩
  rw [ShortComplex.Exact.lift_f]
  abel

end S_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit
end P2MW
export P2MW.S_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit (solution)
