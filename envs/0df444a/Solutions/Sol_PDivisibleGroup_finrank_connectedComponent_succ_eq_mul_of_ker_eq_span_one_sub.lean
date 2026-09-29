-- Prove2me | solution 1 for PDivisibleGroup.finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/abdbe5f9-9e59-500a-9275-91c7c62f6db6

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

universe u v w w'

open PDivisibleGroup.Hopf

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.torsionIdeal height level mk exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal"
namespace CRSE95
p2m_open "PDivisibleGroup"

section Idempotents

variable {A : Type*} [CommRing A]

theorem eq_zero_or_eq_one_of_isIdempotentElem [IsLocalRing A] {e : A}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).1 he)
  · left
    have h1 : (1 - e) = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit h).1 he.one_sub
    have := congrArg (fun x => 1 - x) h1
    simpa using this

theorem apply_eq_one_of_isIdempotentElem {B : Type*} [CommRing B] [IsLocalRing B]
    {S : Type*} [CommRing S] [Nontrivial S]
    (ρ : A →+* B) {e : A} (he : IsIdempotentElem e) (ε : B →+* S) (hε : ε (ρ e) = 1) :
    ρ e = 1 := by
  rcases eq_zero_or_eq_one_of_isIdempotentElem (he.map ρ) with h | h
  · rw [h, map_zero] at hε
    exact absurd hε zero_ne_one
  · exact h

end Idempotents

section Ideals

variable {R : Type*} [CommRing R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

theorem ideal_map_comp [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (I : Ideal A) :
    I.map (g.comp f) = (I.map f).map g :=
  (Ideal.map_map (f : A →+* B) (g : B →+* C)).symm

theorem map_augIdeal_eq_of_surjective [Bialgebra R A] [Bialgebra R B] (φ : A →ₐc[R] B)
    (hφ : Function.Surjective φ) :
    (augIdeal R A).map (φ : A →ₐ[R] B) = augIdeal R B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_augIdeal_iff]
    change Coalgebra.counit (R := R) (φ a) = 0
    rw [CoalgHomClass.counit_comp_apply]
    exact (mem_augIdeal_iff R A a).1 ha
  · intro b hb
    have hφ' : Function.Surjective (φ : A →ₐ[R] B) := hφ
    obtain ⟨a, rfl⟩ := hφ' b
    have ha : a - algebraMap R A (Coalgebra.counit (R := R) a) ∈ augIdeal R A :=
      sub_algebraMap_counit_mem_augIdeal R A a
    have hεa : Coalgebra.counit (R := R) a = 0 := by
      have hb' := (mem_augIdeal_iff R B _).1 hb
      change Coalgebra.counit (R := R) (φ a) = 0 at hb'
      rwa [CoalgHomClass.counit_comp_apply] at hb'
    rw [hεa, map_zero, sub_zero] at ha
    exact Ideal.mem_map_of_mem _ ha

theorem map_torsionIdeal_eq_of_surjective [Bialgebra R A] [Bialgebra R B]
    (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) (n : ℕ) :
    (torsionIdeal R A n).map (φ : A →ₐ[R] B) = torsionIdeal R B n := by
  rw [torsionIdeal, torsionIdeal, ← ideal_map_comp, ← nsmulAlgHom_comp_bialgHom φ n, ideal_map_comp,
    map_augIdeal_eq_of_surjective φ hφ]

end Ideals

section Transport

theorem projective_of_surjective_scalars {C : Type*} [CommRing C] {S : Type*} [CommRing S]
    (ψ : C →+* S) (hψ : Function.Surjective ψ)
    (M : Type*) [AddCommGroup M] [Module S M] [Module C M]
    (hcompat : ∀ (c : C) (m : M), c • m = ψ c • m) [Module.Projective C M] :
    Module.Projective S M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective C M›

  let F : (M →₀ C) →+ (M →₀ S) := (Finsupp.mapRange.addMonoidHom (ψ : C →+ S))
  have hF : ∀ (c : C) (f : M →₀ C), F (c • f) = ψ c • F f := by
    intro c f
    ext m
    simp [F, Finsupp.mapRange.addMonoidHom_apply, smul_eq_mul, map_mul]
  let s' : M →ₗ[S] (M →₀ S) :=
    { toFun := fun m => F (s m)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun r m => by
        obtain ⟨c, rfl⟩ := hψ r
        rw [RingHom.id_apply, ← hcompat, LinearMap.map_smul, hF] }
  refine Module.projective_def'.mpr ⟨s', ?_⟩
  ext m
  have hm : Finsupp.linearCombination C (id : M → M) (s m) = m := by
    have := LinearMap.congr_fun hs m
    simpa using this
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  change Finsupp.linearCombination S (id : M → M) (F (s m)) = m
  conv_rhs => rw [← hm]
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [show F (s m) = Finsupp.mapRange (ψ : C →+ S) (ψ : C →+ S).map_zero (s m) from rfl]
  rw [Finsupp.sum_mapRange_index (by intro m; exact zero_smul _ _)]
  apply Finsupp.sum_congr
  intro x _
  change ψ (s m x) • id x = (s m x) • id x
  rw [← hcompat]

theorem exists_basis_quotient_map {𝓞 : Type*} [CommRing 𝓞] {S : Type*} [CommRing S] [Algebra 𝓞 S]
    {T : Type*} [CommRing T] [Algebra 𝓞 T] [Algebra S T] [IsScalarTower 𝓞 S T]
    {ι : Type*} (b : Module.Basis ι S T) (I : Ideal S)
    (ε : S →ₗ[𝓞] 𝓞) (hε : ∀ o : 𝓞, ε (algebraMap 𝓞 S o) = o)
    (hI : ∀ s : S, s - algebraMap 𝓞 S (ε s) ∈ I) (hI' : ∀ s ∈ I, ε s = 0) :
    ∃ b' : Module.Basis ι 𝓞 (T ⧸ I.map (algebraMap S T)),
      ∀ i, b' i = Ideal.Quotient.mk (I.map (algebraMap S T)) (b i) := by
  classical
  set J : Ideal T := I.map (algebraMap S T) with hJ
  let v : ι → T ⧸ J := fun i => Ideal.Quotient.mk J (b i)

  have hcoord : ∀ y ∈ J, ∀ i, b.repr y i ∈ I := by
    intro y hy
    have hy' : y ∈ (I • ⊤ : Submodule S T) := by
      rw [Ideal.smul_top_eq_map]; exact hy
    refine Submodule.smul_induction_on hy' ?_ ?_
    · intro s hs t _ i
      rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hs
    · intro x y hx hy i
      rw [map_add, Finsupp.add_apply]
      exact I.add_mem (hx i) (hy i)

  have hsm : ∀ (o : 𝓞) (t : T), Ideal.Quotient.mk J (algebraMap 𝓞 S o • t) = o • Ideal.Quotient.mk J t := by
    intro o t
    rw [algebraMap_smul]
    exact Submodule.Quotient.mk_smul J o t
  have hli : LinearIndependent 𝓞 v := by
    rw [linearIndependent_iff']
    intro s g hg i hi

    have hsum : Ideal.Quotient.mk J (∑ j ∈ s, algebraMap 𝓞 S (g j) • b j) = 0 := by
      rw [map_sum]
      simp_rw [hsm]
      exact hg
    have hmem : (∑ j ∈ s, algebraMap 𝓞 S (g j) • b j) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hsum
    have hc := hcoord _ hmem i
    rw [map_sum] at hc
    simp_rw [LinearEquiv.map_smul, Module.Basis.repr_self] at hc
    rw [Finset.sum_apply'] at hc
    simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply] at hc
    rw [Finset.sum_ite_eq' s i] at hc
    rw [if_pos hi] at hc
    have := hI' _ hc
    rwa [hε] at this
  have hsp : ⊤ ≤ Submodule.span 𝓞 (Set.range v) := by
    rintro x -
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ht : t = ∑ i ∈ (b.repr t).support, (b.repr t i) • b i := (b.linearCombination_repr t).symm.trans (Finsupp.linearCombination_apply _ _)
    rw [ht, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsplit : (b.repr t i) • b i =
        algebraMap 𝓞 S (ε (b.repr t i)) • b i + (b.repr t i - algebraMap 𝓞 S (ε (b.repr t i))) • b i := by
      rw [← add_smul, add_sub_cancel]
    rw [hsplit, map_add, hsm]
    have hz : Ideal.Quotient.mk J ((b.repr t i - algebraMap 𝓞 S (ε (b.repr t i))) • b i) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
      exact J.mul_mem_right _ (Ideal.mem_map_of_mem _ (hI _))
    rw [hz, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

end Transport

end PDivisibleGroup.CRSE95

open PDivisibleGroup.CRSE95 in

theorem solution
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (v : ℕ)
    (R₁ : Type w) [CommRing R₁] [HopfAlgebra 𝓞 R₁] [Module.Free 𝓞 R₁] [Module.Finite 𝓞 R₁]
    (ρ₁ : L (v + 1) →ₐc[𝓞] R₁) (e₁ : L (v + 1)) (he₁ : IsIdempotentElem e₁)
    (hε₁ : Coalgebra.counit (R := 𝓞) e₁ = 1) (hρ₁ : Function.Surjective ρ₁)
    (hk₁ : RingHom.ker (ρ₁ : L (v + 1) →ₐ[𝓞] R₁) = Ideal.span {1 - e₁}) (hR₁ : IsLocalRing R₁)
    (R₀ : Type w') [CommRing R₀] [HopfAlgebra 𝓞 R₀] [Module.Free 𝓞 R₀] [Module.Finite 𝓞 R₀]
    (ρ₀ : L v →ₐc[𝓞] R₀) (e₀ : L v) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝓞) e₀ = 1) (hρ₀ : Function.Surjective ρ₀)
    (hk₀ : RingHom.ker (ρ₀ : L v →ₐ[𝓞] R₀) = Ideal.span {1 - e₀}) (hR₀ : IsLocalRing R₀) :
    Module.Free 𝓞 (R₁ ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 R₁ p) ∧
      Module.finrank 𝓞 R₁ =
        Module.finrank 𝓞 (R₁ ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 R₁ p) * Module.finrank 𝓞 R₀ := by
  classical
  haveI : IsLocalRing R₁ := hR₁
  haveI : IsLocalRing R₀ := hR₀

  obtain ⟨⟨e, he⟩, hfinC, hprojC, -, -⟩ :=
    PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
      𝓞 p h L t ht hrankL hkerL v
  haveI := hprojC
  let N : L (v + 1) →ₐ[𝓞] L (v + 1) := nsmulAlgHom 𝓞 (L (v + 1)) p
  let C : Subalgebra 𝓞 (L (v + 1)) := (nsmulAlgHom 𝓞 (L (v + 1)) p).range

  let χ : L v →ₐ[𝓞] L (v + 1) := C.val.comp (e : L v →ₐ[𝓞] C)
  have hχt : ∀ a : L (v + 1), χ (t v a) = N a := fun a => he a
  have hNχ : (nsmulAlgHom 𝓞 (L (v + 1)) p) = χ.comp (t v : L (v + 1) →ₐ[𝓞] L v) := by
    ext a
    exact (hχt a).symm

  have hεχ : ∀ b : L v, Coalgebra.counit (R := 𝓞) (χ b) = Coalgebra.counit (R := 𝓞) b := by
    intro b
    obtain ⟨a, rfl⟩ := ht v b
    rw [hχt]
    change Coalgebra.counit (R := 𝓞) (nsmulAlgHom 𝓞 (L (v + 1)) p a) = _
    rw [counit_nsmulAlgHom]
    exact (CoalgHomClass.counit_comp_apply (t v) a).symm

  have hρ₁χe₀ : ρ₁ (χ e₀) = 1 := by
    have hid : IsIdempotentElem (χ e₀) := he₀.map χ
    refine apply_eq_one_of_isIdempotentElem ((ρ₁ : L (v + 1) →ₐ[𝓞] R₁) : L (v + 1) →+* R₁) hid
      ((Bialgebra.counitAlgHom 𝓞 R₁ : R₁ →ₐ[𝓞] 𝓞) : R₁ →+* 𝓞) ?_
    change Coalgebra.counit (R := 𝓞) (ρ₁ (χ e₀)) = 1
    rw [CoalgHomClass.counit_comp_apply, hεχ, hε₀]

  have hkerle : RingHom.ker (ρ₀ : L v →ₐ[𝓞] R₀) ≤
      RingHom.ker ((ρ₁ : L (v + 1) →ₐ[𝓞] R₁).comp χ) := by
    rw [hk₀, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change ρ₁ (χ (1 - e₀)) = 0
    rw [map_sub, map_one, map_sub, map_one, hρ₁χe₀, sub_self]
  let φ : R₀ →ₐ[𝓞] R₁ :=
    AlgHom.liftOfSurjective (ρ₀ : L v →ₐ[𝓞] R₀) hρ₀ ((ρ₁ : L (v + 1) →ₐ[𝓞] R₁).comp χ) hkerle
  have hφρ₀ : ∀ b : L v, φ (ρ₀ b) = ρ₁ (χ b) := fun b =>
    DFunLike.congr_fun (AlgHom.liftOfSurjective_comp (ρ₀ : L v →ₐ[𝓞] R₀) hρ₀ _ hkerle) b
  have hφρ₀' : φ.comp (ρ₀ : L v →ₐ[𝓞] R₀) = (ρ₁ : L (v + 1) →ₐ[𝓞] R₁).comp χ := by
    ext b
    exact hφρ₀ b

  letI : Algebra R₀ R₁ := φ.toRingHom.toAlgebra
  have halg : ∀ r : R₀, algebraMap R₀ R₁ r = φ r := fun _ => rfl
  haveI : IsScalarTower 𝓞 R₀ R₁ := IsScalarTower.of_algebraMap_eq fun o => (φ.commutes o).symm
  haveI : Module.Finite R₀ R₁ := Module.Finite.of_restrictScalars_finite 𝓞 R₀ R₁

  letI instCR₁ : Module C R₁ :=
    Module.compHom R₁ (((ρ₁ : L (v + 1) →ₐ[𝓞] R₁) : L (v + 1) →+* R₁).comp C.val.toRingHom)
  have hCsmul : ∀ (c : C) (x : R₁), c • x = ρ₁ (c : L (v + 1)) * x := fun _ _ => rfl

  have hρ₁e₁ : ρ₁ e₁ = 1 := by
    have hmem : (1 : L (v + 1)) - e₁ ∈ RingHom.ker (ρ₁ : L (v + 1) →ₐ[𝓞] R₁) := by
      rw [hk₁]; exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
    exact hmem.symm
  have hmul_e₁ : ∀ a a' : L (v + 1), ρ₁ a = ρ₁ a' → a * e₁ = a' * e₁ := by
    intro a a' haa'
    have hmem : a - a' ∈ RingHom.ker (ρ₁ : L (v + 1) →ₐ[𝓞] R₁) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact haa'
    rw [hk₁, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h0 : (a - a') * e₁ = 0 := by
      rw [hc, mul_comm (1 - e₁) c, mul_assoc, sub_mul, one_mul, he₁.eq, sub_self, mul_zero]
    rwa [sub_mul, sub_eq_zero] at h0
  have hρ₁s : Function.Surjective (ρ₁ : L (v + 1) → R₁) := hρ₁
  let σ : R₁ → L (v + 1) := Function.surjInv hρ₁s
  have hσ : ∀ x, ρ₁ (σ x) = x := Function.surjInv_eq hρ₁s
  have hσρ : ∀ a, σ (ρ₁ a) * e₁ = a * e₁ := fun a => hmul_e₁ _ _ (hσ _)
  let i : R₁ →ₗ[C] L (v + 1) :=
    { toFun := fun x => σ x * e₁
      map_add' := fun x y => by
        change σ (x + y) * e₁ = σ x * e₁ + σ y * e₁
        conv_lhs => rw [← hσ x, ← hσ y, ← map_add]
        rw [hσρ, add_mul]
      map_smul' := fun c x => by
        change σ (c • x) * e₁ = (c : L (v + 1)) * (σ x * e₁)
        rw [hCsmul]
        conv_lhs => rw [← hσ x, ← map_mul]
        rw [hσρ, mul_assoc] }
  let sC : L (v + 1) →ₗ[C] R₁ :=
    { toFun := fun a => ρ₁ a
      map_add' := fun a a' => map_add _ _ _
      map_smul' := fun c a => by
        change ρ₁ ((c : L (v + 1)) * a) = ρ₁ (c : L (v + 1)) * ρ₁ a
        exact map_mul _ _ _ }
  have hsi : sC.comp i = LinearMap.id := by
    ext x
    change ρ₁ (σ x * e₁) = x
    rw [map_mul, hσ, hρ₁e₁, mul_one]
  haveI : Module.Projective C R₁ := Module.Projective.of_split i sC hsi

  let ψ : C →+* R₀ := ((ρ₀ : L v →ₐ[𝓞] R₀) : L v →+* R₀).comp ((e.symm : C →ₐ[𝓞] L v) : C →+* L v)
  have hψ : Function.Surjective ψ := hρ₀.comp e.symm.surjective
  have hcompat : ∀ (c : C) (m : R₁), c • m = ψ c • m := by
    intro c m
    rw [hCsmul, Algebra.smul_def, halg]
    change ρ₁ (c : L (v + 1)) * m = φ (ρ₀ (e.symm c)) * m
    rw [hφρ₀]
    congr 1
    change ρ₁ (c : L (v + 1)) = ρ₁ ((e (e.symm c) : C) : L (v + 1))
    rw [AlgEquiv.apply_symm_apply]
  haveI : Module.Projective R₀ R₁ := projective_of_surjective_scalars ψ hψ R₁ hcompat
  haveI : Module.Flat R₀ R₁ := inferInstance
  haveI : Module.Free R₀ R₁ := Module.free_of_flat_of_isLocalRing

  have htors : torsionIdeal 𝓞 R₁ p = (augIdeal 𝓞 R₀).map (algebraMap R₀ R₁) := by
    have h1 := map_torsionIdeal_eq_of_surjective ρ₁ hρ₁ p
    rw [← h1]
    change ((augIdeal 𝓞 (L (v + 1))).map (nsmulAlgHom 𝓞 (L (v + 1)) p)).map (ρ₁ : L (v + 1) →ₐ[𝓞] R₁) = _
    rw [hNχ, ideal_map_comp, map_augIdeal_eq_of_surjective (t v) (ht v), ← ideal_map_comp, ← hφρ₀',
      ideal_map_comp, map_augIdeal_eq_of_surjective ρ₀ hρ₀]
    rfl

  let b := Module.Free.chooseBasis R₀ R₁
  obtain ⟨b', hb'⟩ := exists_basis_quotient_map b (augIdeal 𝓞 R₀)
    (Coalgebra.counit : R₀ →ₗ[𝓞] 𝓞) (fun o => Bialgebra.counit_algebraMap o)
    (sub_algebraMap_counit_mem_augIdeal 𝓞 R₀) (fun s hs => (mem_augIdeal_iff 𝓞 R₀ s).1 hs)
  let E : (R₁ ⧸ torsionIdeal 𝓞 R₁ p) ≃ₐ[𝓞] (R₁ ⧸ (augIdeal 𝓞 R₀).map (algebraMap R₀ R₁)) :=
    Ideal.quotientEquivAlgOfEq 𝓞 htors
  haveI : Module.Free 𝓞 (R₁ ⧸ (augIdeal 𝓞 R₀).map (algebraMap R₀ R₁)) := Module.Free.of_basis b'
  have hfree : Module.Free 𝓞 (R₁ ⧸ torsionIdeal 𝓞 R₁ p) := Module.Free.of_equiv E.symm.toLinearEquiv
  have hrank1 : Module.finrank 𝓞 (R₁ ⧸ torsionIdeal 𝓞 R₁ p) = Module.finrank R₀ R₁ := by
    rw [E.toLinearEquiv.finrank_eq, Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_chooseBasisIndex]
  refine ⟨hfree, ?_⟩
  rw [hrank1, mul_comm, Module.finrank_mul_finrank]

end S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
end P2MW
export P2MW.S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub (solution)
