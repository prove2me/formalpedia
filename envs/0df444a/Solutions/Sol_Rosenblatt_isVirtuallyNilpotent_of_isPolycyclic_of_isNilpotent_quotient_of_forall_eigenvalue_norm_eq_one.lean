-- Prove2me | solution 1 for Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T11:34:19.365991+00:00
-- url     : https://prove2.me/submissions/f1297045-19e1-47b2-a7b3-c78f3c8f6054

import Definitions.Def_MilnorWolf_Growth
import Mathlib

/-!
# Rosenblatt, Theorem 4.12: the linear-algebra leaf

Setting: a group `G` with a normal subgroup `A` identified with `ℤ^k` by `e`, integer matrices
`T g` giving conjugation by `g` in these coordinates, `G ⧸ A` nilpotent, and every complex
eigenvalue of every `T g` of modulus `1`.  Conclusion: `G` is virtually nilpotent.

The proof has three steps.

* **Finitely many eigenvalues** (`finite_eigenvalues_of_norm_le_one`).  The characteristic
  polynomial of an integer `k × k` matrix whose complex eigenvalues lie in the closed unit disc is
  monic of degree `k` with coefficients bounded by `2^k`.  There are finitely many such
  polynomials, so all eigenvalues of all `T g` lie in one finite set.
* **Virtual unipotence** (`virtUnip_of_finite_eigenvalues`, general linear algebra).  Let a
  nilpotent group act linearly on a vector space of dimension `n` over an algebraically closed
  field, with every eigenvalue of every element in a fixed finite set.  Then some finite-index
  subgroup `Γ₀` makes every product `(ρ γ₁ - 1) ⋯ (ρ γₙ - 1)` with `γᵢ ∈ Γ₀` vanish.  The proof is
  a strong induction on `n`.  If every element acts by a scalar, those scalars lie in the finite
  set and the kernel has finite index.  Otherwise take an element `y` of the upper central series,
  of least height, acting non-scalarly.  Commutators with `y` act by scalars from the finite set,
  so `ρ y` commutes with a finite-index subgroup `Γ₁`, and an eigenspace of `ρ y` is a nonzero
  proper `Γ₁`-invariant subspace; recurse on it and on the quotient.  No Kolchin, Engel or
  Kronecker theorem is needed.
* **The chain** (`leafChain`).  The map `g ↦ T g` kills `A` (`A` is abelian), so it factors
  through the nilpotent group `G ⧸ A`, which therefore acts on `ℂ^k` (`leafRhoBar`).  With `G₀`
  the preimage of the subgroup given by the previous step, let `N_j ≤ G₀` consist of the images
  of vectors killed by all products of `j` factors `T g - 1`, `g ∈ G₀`.  Then `N_0 = 1`,
  `⁅N_{j+1}, G₀⁆ ≤ N_j`, every element of `A ∩ G₀` lies in `N_k`, and some term of the lower
  central series of `G₀` lies in `A`; so a later term is trivial
  (`isNilpotent_of_lowerCentralSeries_le_chain`).

The polycyclic hypothesis of the statement is not used by this proof.

The section `LinearAlgebra` is independent of the statement's data.
-/

open scoped Matrix
open Module
open scoped commutatorElement

namespace Rosenblatt

universe u v

/-! ## General linear algebra: virtually unipotent representations of nilpotent groups -/

section LinearAlgebra

section Basic
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- An eigenvalue of the restriction of `f` to an invariant subspace is an eigenvalue of `f`. -/
theorem hasEigenvalue_of_restrict {f : End K V} {p : Submodule K V} (hf : ∀ x ∈ p, f x ∈ p)
    {μ : K} (h : Module.End.HasEigenvalue (f.restrict hf) μ) : f.HasEigenvalue μ := by
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := (x : V)) ⟨?_, ?_⟩
  · exact Module.End.eigenspace_restrict_le_eigenspace f hf μ ⟨x, hx.1, rfl⟩
  · exact fun h0 => hx.2 (Subtype.ext h0)

/-- In finite dimension, an eigenvalue of the map induced by `f` on a quotient by an invariant
subspace is an eigenvalue of `f`. -/
theorem hasEigenvalue_of_mapQ [FiniteDimensional K V] {f : End K V} {p : Submodule K V}
    (hf : p ≤ p.comap f) {μ : K} (h : Module.End.HasEigenvalue (p.mapQ p f hf) μ) :
    f.HasEigenvalue μ := by
  by_contra hne
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective p x
  set g : End K V := f - algebraMap K (End K V) μ with hg
  -- `g = f - μ` is injective, hence bijective on `p`
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.mpr fun y hy => ?_
    · by_contra hy0
      exact hne (Module.End.hasEigenvalue_of_hasEigenvector (x := y)
        ⟨by simpa [Module.End.mem_eigenspace_iff, hg, sub_eq_zero] using hy, hy0⟩)
  have hgp : ∀ y ∈ p, g y ∈ p := fun y hy => by
    simp only [hg, LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact p.sub_mem (hf hy) (p.smul_mem μ hy)
  have hsurj : Function.Surjective (g.restrict hgp) :=
    LinearMap.injective_iff_surjective.mp
      (fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)))
  have hgv : g v ∈ p := by
    have h1 := Module.End.mem_eigenspace_iff.mp hx.1
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply] at h1
    simp [hg, Submodule.Quotient.mk_sub, h1, Submodule.Quotient.mk_smul]
  obtain ⟨w, hw⟩ := hsurj ⟨g v, hgv⟩
  have : (w : V) = v := hinj (by simpa using congrArg Subtype.val hw)
  apply hx.2
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact this ▸ w.2

/-- A map whose `μ`-eigenspace is everything is the scalar `μ`. -/
theorem eq_algebraMap_of_eigenspace_eq_top {f : End K V} {μ : K} (h : f.eigenspace μ = ⊤) :
    f = algebraMap K (End K V) μ := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ f.eigenspace μ := h ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hx
  simp [hx]

/-- On a nonzero space, `c` is an eigenvalue of the scalar `c`. -/
theorem hasEigenvalue_algebraMap [Nontrivial V] (c : K) :
    (algebraMap K (End K V) c).HasEigenvalue c := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    ⟨Module.End.mem_eigenspace_iff.mpr (by simp), hx⟩

/-- The restriction of a representation to an invariant subspace. -/
def restrictHom {Γ : Type*} [Group Γ] (ρ : Γ →* End K V) (W : Submodule K V)
    (hW : ∀ γ, ∀ x ∈ W, ρ γ x ∈ W) : Γ →* End K W where
  toFun γ := (ρ γ).restrict (hW γ)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- The representation induced on the quotient by an invariant subspace. -/
def quotHom {Γ : Type*} [Group Γ] (ρ : Γ →* End K V) (W : Submodule K V)
    (hW : ∀ γ, ∀ x ∈ W, ρ γ x ∈ W) : Γ →* End K (V ⧸ W) where
  toFun γ := W.mapQ W (ρ γ) (fun x hx => hW γ x hx)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- Products of factors `ρ γ - 1` commute with restriction to an invariant subspace. -/
theorem prod_restrictHom_apply {Γ : Type*} [Group Γ] (ρ : Γ →* End K V) (W : Submodule K V)
    (hW : ∀ γ, ∀ x ∈ W, ρ γ x ∈ W) (l : List Γ) (w : W) :
    (((l.map (fun γ => restrictHom ρ W hW γ - 1)).prod w : W) : V)
      = (l.map (fun γ => ρ γ - 1)).prod (w : V) := by
  induction l with
  | nil => simp
  | cons γ l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [← ih]; rfl

/-- Products of factors `ρ γ - 1` commute with passing to the quotient by an invariant
subspace. -/
theorem prod_quotHom_mk {Γ : Type*} [Group Γ] (ρ : Γ →* End K V) (W : Submodule K V)
    (hW : ∀ γ, ∀ x ∈ W, ρ γ x ∈ W) (l : List Γ) (v : V) :
    (l.map (fun γ => quotHom ρ W hW γ - 1)).prod (W.mkQ v)
      = W.mkQ ((l.map (fun γ => ρ γ - 1)).prod v) := by
  induction l with
  | nil => simp
  | cons γ l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, ih, map_sub]
    rfl

end Basic

section Key
variable {K : Type*} [Field K]

/-- `f` is a scalar multiple of the identity. -/
def IsScalar {V : Type*} [AddCommGroup V] [Module K V] (f : End K V) : Prop :=
  ∃ c : K, f = algebraMap K (End K V) c

/-- A representation by scalars taken from a finite set has a kernel of finite index. -/
theorem finiteIndex_ker_of_forall_isScalar {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V]
    [Module K V] (ψ : Γ →* End K V) (S : Set K) (hS : S.Finite)
    (hψ : ∀ γ, ∃ c ∈ S, ψ γ = algebraMap K (End K V) c) :
    (ψ.toHomUnits.ker).FiniteIndex := by
  have hfin : (ψ.toHomUnits.range : Set (End K V)ˣ).Finite := by
    refine ((hS.image (algebraMap K (End K V))).preimage
      (Units.val_injective.injOn)).subset ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨c, hcS, hc⟩ := hψ h
    exact ⟨c, hcS, by rw [← hc]; rfl⟩
  have : Finite ψ.toHomUnits.range := hfin.to_subtype
  exact Subgroup.finiteIndex_ker _

/-- If `Z_j(Γ)` acts by scalars, eigenvalues lie in a finite set `S`, and `y ∈ Z_{j+1}(Γ)`, then
`ρ y` commutes with `ρ h` for all `h` in a finite-index subgroup.  The map `h ↦ ρ ⁅y, h⁆` is a
homomorphism into scalars from `S`; its kernel is the subgroup. -/
theorem finiteIndex_centralizer_of_mem_upperCentralSeries {Γ : Type*} [Group Γ] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Γ →* End K V) (S : Set K) (hS : S.Finite)
    (hρS : ∀ γ μ, (ρ γ).HasEigenvalue μ → μ ∈ S) {j : ℕ}
    (hj : ∀ z ∈ Subgroup.upperCentralSeries Γ j, IsScalar (ρ z)) {y : Γ}
    (hy : y ∈ Subgroup.upperCentralSeries Γ (j + 1)) :
    ∃ Γ₁ : Subgroup Γ, Γ₁.FiniteIndex ∧ ∀ h ∈ Γ₁, Commute (ρ y) (ρ h) := by
  have hsc : ∀ h : Γ, ∃ c ∈ S, ρ ⁅y, h⁆ = algebraMap K (End K V) c := by
    intro h
    obtain ⟨c, hc⟩ := hj _ ((Subgroup.mem_upperCentralSeries_succ_iff).mp hy h)
    refine ⟨c, hρS ⁅y, h⁆ _ ?_, hc⟩
    rw [hc]; exact hasEigenvalue_algebraMap c
  have hid : ∀ a b : Γ, ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
    intro a b; simp only [commutatorElement_def]; group
  let ψ : Γ →* (End K V)ˣ :=
    { toFun := fun h => ρ.toHomUnits ⁅y, h⁆
      map_one' := by simp
      map_mul' := by
        intro a b
        ext1
        simp only [MonoidHom.coe_toHomUnits, Units.val_mul]
        obtain ⟨c, -, hc⟩ := hsc b
        rw [hid, map_mul, map_mul, map_mul, hc,
          ← (Algebra.commute_algebraMap_left c (ρ a)).eq, mul_assoc, ← map_mul,
          mul_inv_cancel, map_one, mul_one] }
  have hfin : (ψ.range : Set (End K V)ˣ).Finite := by
    refine ((hS.image (algebraMap K (End K V))).preimage
      (Units.val_injective.injOn)).subset ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨c, hcS, hc⟩ := hsc h
    exact ⟨c, hcS, by rw [← hc]; rfl⟩
  have : Finite ψ.range := hfin.to_subtype
  refine ⟨ψ.ker, inferInstance, fun h hh => ?_⟩
  have h1 : ρ ⁅y, h⁆ = 1 := by
    exact congrArg Units.val (MonoidHom.mem_ker.mp hh)
  have h2 : y * h = ⁅y, h⁆ * (h * y) := by simp only [commutatorElement_def]; group
  show ρ y * ρ h = ρ h * ρ y
  rw [← map_mul, ← map_mul, h2, map_mul, h1, one_mul]

/-- If a representation of a nilpotent group is not by scalars, some `y ∈ Z_{j+1}` acts
non-scalarly while all of `Z_j` acts by scalars. -/
theorem exists_nonscalar_of_nilpotent {Γ : Type*} [Group Γ] [Group.IsNilpotent Γ] {V : Type*}
    [AddCommGroup V] [Module K V] (ρ : Γ →* End K V) (hns : ∃ γ, ¬ IsScalar (ρ γ)) :
    ∃ j y, (∀ z ∈ Subgroup.upperCentralSeries Γ j, IsScalar (ρ z)) ∧
      y ∈ Subgroup.upperCentralSeries Γ (j + 1) ∧ ¬ IsScalar (ρ y) := by
  classical
  let P : ℕ → Prop := fun j => ∀ z ∈ Subgroup.upperCentralSeries Γ j, IsScalar (ρ z)
  obtain ⟨c, hc⟩ := Group.IsNilpotent.nilpotent Γ
  have hex : ∃ j, ¬ P j := by
    refine ⟨c, fun h => ?_⟩
    obtain ⟨γ, hγ⟩ := hns
    exact hγ (h γ (hc ▸ Subgroup.mem_top γ))
  have hP0 : P 0 := by
    intro z hz
    rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hz
    subst hz
    exact ⟨1, by simp⟩
  have hm0 : Nat.find hex ≠ 0 := fun h => Nat.find_spec hex (h ▸ hP0)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hPj : P j := by
    by_contra h
    exact Nat.find_min hex (by omega : j < Nat.find hex) h
  have hnP : ¬ P (j + 1) := by have := Nat.find_spec hex; rwa [hj] at this
  simp only [P, not_forall] at hnP
  obtain ⟨y, hy, hys⟩ := hnP
  exact ⟨j, y, hPj, hy, hys⟩

/-- `ρ` is *virtually unipotent of length `n`*: on some finite-index subgroup, every product of
`n` factors `ρ γ - 1` vanishes. -/
def VirtUnip {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Γ →* End K V) (n : ℕ) : Prop :=
  ∃ Γ₀ : Subgroup Γ, Γ₀.FiniteIndex ∧ ∀ l : List Γ, l.length = n → (∀ x ∈ l, x ∈ Γ₀) →
    (l.map (fun x => ρ x - 1)).prod = 0

/-- A finite-index subgroup of a finite-index subgroup has finite index. -/
theorem finiteIndex_map_subtype_of_finiteIndex {G : Type*} [Group G] (K : Subgroup G)
    [K.FiniteIndex] (H : Subgroup K) [H.FiniteIndex] : (H.map K.subtype).FiniteIndex := by
  refine ⟨?_⟩
  rw [Subgroup.index_map, K.ker_subtype, sup_bot_eq, K.range_subtype]
  exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

/-- The recursion step: if a finite-index `Γ₁` preserves `W`, and its representations on `W`
and on `V ⧸ W` are virtually unipotent of lengths `dim W` and `dim V/W`, then `ρ` is virtually
unipotent of length `dim V`. -/
theorem virtUnip_of_invariant {Γ : Type u} [Group Γ] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Γ →* End K V) (Γ₁ : Subgroup Γ) [Γ₁.FiniteIndex]
    (W : Submodule K V) (hW : ∀ γ ∈ Γ₁, ∀ x ∈ W, ρ γ x ∈ W)
    (hWQ : VirtUnip (restrictHom (ρ.comp Γ₁.subtype) W (fun γ => hW γ γ.2))
      (finrank K W))
    (hQ : VirtUnip (quotHom (ρ.comp Γ₁.subtype) W (fun γ => hW γ γ.2))
      (finrank K (V ⧸ W))) :
    VirtUnip ρ (finrank K V) := by
  obtain ⟨ΓW, hΓW, hWprod⟩ := hWQ
  obtain ⟨ΓQ, hΓQ, hQprod⟩ := hQ
  refine ⟨(ΓW ⊓ ΓQ).map Γ₁.subtype, finiteIndex_map_subtype_of_finiteIndex Γ₁ _, ?_⟩
  intro l hl hmem
  -- every entry lies in `Γ₁`, and its lift lies in `ΓW ⊓ ΓQ`
  have h1 : ∀ x ∈ l, x ∈ Γ₁ := fun x hx => by
    obtain ⟨x', -, rfl⟩ := Subgroup.mem_map.mp (hmem x hx); exact x'.2
  have hlift : ∀ (l' : List Γ) (h' : ∀ x ∈ l', x ∈ Γ₁),
      (∀ x ∈ l', x ∈ (ΓW ⊓ ΓQ).map Γ₁.subtype) →
      ∀ x ∈ l'.pmap (fun x hx => (⟨x, hx⟩ : Γ₁)) h', x ∈ ΓW ⊓ ΓQ := by
    intro l' h' hm x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_pmap.mp hx
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp (hm a ha)
    have : x' = ⟨a, h' a ha⟩ := Subtype.ext hxx
    exact this ▸ hx'
  have hmapeq : ∀ (l' : List Γ) (h' : ∀ x ∈ l', x ∈ Γ₁),
      (l'.pmap (fun x hx => (⟨x, hx⟩ : Γ₁)) h').map (fun γ => (ρ.comp Γ₁.subtype) γ - 1)
        = l'.map (fun x => ρ x - 1) := by
    intro l' h'
    rw [List.map_pmap]; exact List.pmap_eq_map (f := fun x => ρ x - 1) h'
  -- split the product as (first `dim W` factors) * (last `dim V/W` factors)
  set a := finrank K W
  have hsplit := List.take_append_drop a l
  rw [← hsplit, List.map_append, List.prod_append]
  set l₁ := l.take a
  set l₂ := l.drop a
  have hl₁ : l₁.length = a := by
    have := Submodule.finrank_quotient_add_finrank W; simp [l₁]; omega
  have hl₂ : l₂.length = finrank K (V ⧸ W) := by
    have := Submodule.finrank_quotient_add_finrank W; simp [l₂]; omega
  have h1₁ : ∀ x ∈ l₁, x ∈ Γ₁ := fun x hx => h1 x (List.mem_of_mem_take hx)
  have h1₂ : ∀ x ∈ l₂, x ∈ Γ₁ := fun x hx => h1 x (List.mem_of_mem_drop hx)
  ext v
  simp only [Module.End.mul_apply, LinearMap.zero_apply]
  -- the tail maps `V` into `W`
  have hQ0 := hQprod (l₂.pmap (fun x hx => (⟨x, hx⟩ : Γ₁)) h1₂) (by simp [hl₂])
    (fun x hx => (hlift l₂ h1₂ (fun x hx => hmem x (List.mem_of_mem_drop hx)) x hx).2)
  have hv : (l₂.map (fun x => ρ x - 1)).prod v ∈ W := by
    have := prod_quotHom_mk (ρ.comp Γ₁.subtype) W (fun γ => hW γ γ.2)
      (l₂.pmap (fun x hx => (⟨x, hx⟩ : Γ₁)) h1₂) v
    rw [hQ0, hmapeq] at this
    exact (Submodule.Quotient.mk_eq_zero W).mp (by simpa using this.symm)
  -- the head kills `W`
  have hW0 := hWprod (l₁.pmap (fun x hx => (⟨x, hx⟩ : Γ₁)) h1₁) (by simp [hl₁])
    (fun x hx => (hlift l₁ h1₁ (fun x hx => hmem x (List.mem_of_mem_take hx)) x hx).1)
  have := prod_restrictHom_apply (ρ.comp Γ₁.subtype) W (fun γ => hW γ γ.2)
    (l₁.pmap (fun x hx => (⟨x, hx⟩ : Γ₁)) h1₁) ⟨_, hv⟩
  rw [hW0, hmapeq] at this
  simpa using this.symm

/-- **Key theorem.**  Let `K` be algebraically closed, `Γ` nilpotent, `ρ` a representation of `Γ`
on a space of dimension `n`, and suppose every eigenvalue of every `ρ γ` lies in a finite set
`S`.  Then there is a finite-index subgroup `Γ₀` such that every product
`(ρ γ₁ - 1) ⋯ (ρ γₙ - 1)` with all `γᵢ ∈ Γ₀` is zero. -/
theorem virtUnip_of_finite_eigenvalues [IsAlgClosed K] :
    ∀ (n : ℕ) {Γ : Type u} [Group Γ] [Group.IsNilpotent Γ] {V : Type v} [AddCommGroup V]
      [Module K V] [FiniteDimensional K V], finrank K V = n →
      ∀ (ρ : Γ →* End K V) (S : Set K), S.Finite →
      (∀ γ μ, (ρ γ).HasEigenvalue μ → μ ∈ S) → VirtUnip ρ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ _ V _ _ _ hn ρ S hS hρS
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `V = 0`
    subst h0
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    exact ⟨⊤, inferInstance, fun l _ _ => Subsingleton.elim _ _⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
  by_cases hall : ∀ γ, IsScalar (ρ γ)
  · -- every `ρ γ` is a scalar: the kernel has finite index
    have hall' : ∀ γ, ∃ c ∈ S, ρ γ = algebraMap K (End K V) c := fun γ => by
      obtain ⟨c, hc⟩ := hall γ
      exact ⟨c, hρS γ c (hc ▸ hasEigenvalue_algebraMap c), hc⟩
    refine ⟨ρ.toHomUnits.ker, finiteIndex_ker_of_forall_isScalar ρ S hS hall', ?_⟩
    intro l hl hmem
    obtain ⟨x, l', rfl⟩ := List.exists_cons_of_length_pos (hl ▸ hpos)
    have hx : ρ x = 1 := congrArg Units.val (MonoidHom.mem_ker.mp (hmem x List.mem_cons_self))
    simp [hx]
  · -- a non-scalar `ρ y` commuting with a finite-index subgroup
    simp only [not_forall] at hall
    obtain ⟨j, y, hj, hy, hys⟩ := exists_nonscalar_of_nilpotent ρ hall
    obtain ⟨Γ₁, hΓ₁, hcomm⟩ :=
      finiteIndex_centralizer_of_mem_upperCentralSeries ρ S hS hρS hj hy
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ y)
    set W := (ρ y).eigenspace μ with hWdef
    have hW : ∀ γ ∈ Γ₁, ∀ x ∈ W, ρ γ x ∈ W := fun γ hγ x hx =>
      Module.End.mapsTo_genEigenspace_of_comm (hcomm γ hγ) μ 1 hx
    have hWtop : W ≠ ⊤ := fun h => hys ⟨μ, eq_algebraMap_of_eigenspace_eq_top h⟩
    have hWbot : W ≠ ⊥ := hμ
    have hWlt : finrank K W < n := hn ▸ Submodule.finrank_lt hWtop
    have hWpos : 0 < finrank K W :=
      Nat.pos_of_ne_zero fun h => hWbot (Submodule.finrank_eq_zero.mp h)
    have hQlt : finrank K (V ⧸ W) < n := by
      have := Submodule.finrank_quotient_add_finrank W
      omega
    subst hn
    refine virtUnip_of_invariant ρ Γ₁ W hW ?_ ?_
    · exact ih _ hWlt rfl _ S hS fun γ μ' h =>
        hρS γ μ' (hasEigenvalue_of_restrict (hW γ γ.2) h)
    · exact ih _ hQlt rfl _ S hS fun γ μ' h =>
        hρS γ μ' (hasEigenvalue_of_mapQ (fun x hx => hW γ γ.2 x hx) h)

end Key

end LinearAlgebra

/-! ## Two general auxiliary facts -/

section Aux

/-- A group is nilpotent if some term of its lower central series lies in the top term `N m` of
a chain of subgroups with `N 0 = ⊥` and `⁅N (j+1), G⁆ ≤ N j`. -/
theorem isNilpotent_of_lowerCentralSeries_le_chain {G : Type*} [Group G] (N : ℕ → Subgroup G)
    (h0 : N 0 = ⊥) (hstep : ∀ j, ∀ x ∈ N (j + 1), ∀ g : G, ⁅x, g⁆ ∈ N j) {c m : ℕ}
    (hc : (⊤ : Subgroup G).lowerCentralSeries c ≤ N m) : Group.IsNilpotent G := by
  have key : ∀ i ≤ m, (⊤ : Subgroup G).lowerCentralSeries (c + i) ≤ N (m - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using hc
    | succ i ih =>
      intro hi
      rw [← add_assoc, Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
      intro x hx g _
      exact hstep (m - (i + 1)) x (by
        rw [show m - (i + 1) + 1 = m - i by omega]; exact ih (by omega) hx) g
  refine Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c + m, ?_⟩
  have := key m le_rfl
  rw [Nat.sub_self, h0] at this
  exact eq_bot_iff.mpr this

/-- The complex eigenvalues of all integer `k × k` matrices whose complex eigenvalues lie in the
closed unit disc form a finite set.  (The characteristic polynomial is monic of degree `k` with
integer coefficients bounded by `2^k`.) -/
theorem finite_eigenvalues_of_norm_le_one (k : ℕ) :
    {μ : ℂ | ∃ M : Matrix (Fin k) (Fin k) ℤ,
      (∀ (φ : ℂ) (v : Fin k → ℂ), v ≠ 0 → (M.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v →
        ‖φ‖ ≤ 1) ∧
      Module.End.HasEigenvalue (Matrix.toLin' (M.map (fun z : ℤ => (z : ℂ)))) μ}.Finite := by
  classical
  refine (Polynomial.bUnion_roots_finite (Int.castRingHom ℂ) k
    (Set.finite_Icc (-(2 ^ k : ℤ)) (2 ^ k))).subset ?_
  rintro μ ⟨M, hM, hμ⟩
  set χ := M.charpoly with hχ
  have hmap : χ.map (Int.castRingHom ℂ) = (M.map (Int.castRingHom ℂ)).charpoly :=
    (Matrix.charpoly_map M _).symm
  have hdeg : χ.natDegree = k := by
    rw [hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- the eigenvalues of the cast matrix are the roots of `χ` over `ℂ`
  have hroot : ∀ r : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' (M.map (fun z : ℤ => (z : ℂ)))) r ↔
        r ∈ (χ.map (Int.castRingHom ℂ)).roots := by
    intro r
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
      Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.mem_roots
        ((Matrix.charpoly_monic M).map _).ne_zero, hmap]
    rfl
  have hnorm : ∀ r ∈ (χ.map (Int.castRingHom ℂ)).roots, ‖r‖ ≤ 1 := by
    intro r hr
    obtain ⟨v, hv⟩ := ((hroot r).mpr hr).exists_hasEigenvector
    refine hM r v hv.2 ?_
    have := Module.End.mem_eigenspace_iff.mp hv.1
    rwa [Matrix.toLin'_apply] at this
  simp only [Set.mem_iUnion]
  refine ⟨χ, ⟨hdeg.le, fun i => ?_⟩, ?_⟩
  · -- coefficient bound `|χᵢ| ≤ C(k, i) ≤ 2^k`
    have hb := Polynomial.coeff_le_of_roots_le (f := Int.castRingHom ℂ) i
      (Matrix.charpoly_monic M) (IsAlgClosed.splits _) hnorm
    rw [Polynomial.coeff_map, one_pow, one_mul, hdeg, eq_intCast, Complex.norm_intCast] at hb
    have h2 : ((k.choose i : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow k i
    have h3 : |(χ.coeff i : ℝ)| ≤ (2 ^ k : ℝ) := hb.trans h2
    have h4 : |χ.coeff i| ≤ 2 ^ k := by exact_mod_cast h3
    exact abs_le.mp h4
  · simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (hroot μ).mp hμ

end Aux

/-! ## The statement's data -/

section Data
variable {G : Type*} [Group G] {k : ℕ} (A : Subgroup G)
  (e : A ≃* Multiplicative (Fin k → ℤ)) (T : G → Matrix (Fin k) (Fin k) ℤ)

/-- The embedding of `ℤ^k` into `G` determined by `e`. -/
def leafEmb (z : Fin k → ℤ) : G := ((e.symm (Multiplicative.ofAdd z) : A) : G)

theorem leafEmb_injective : Function.Injective (leafEmb A e) := fun _ _ h =>
  Multiplicative.ofAdd.injective (e.symm.injective (Subtype.ext h))

theorem leafEmb_add (z w : Fin k → ℤ) :
    leafEmb A e (z + w) = leafEmb A e z * leafEmb A e w := by
  show ((e.symm (Multiplicative.ofAdd (z + w)) : A) : G) = _
  rw [show Multiplicative.ofAdd (z + w)
      = Multiplicative.ofAdd z * Multiplicative.ofAdd w from rfl, map_mul]
  rfl

theorem leafEmb_zero : leafEmb A e 0 = 1 := by
  have h := leafEmb_add A e 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem leafEmb_neg (z : Fin k → ℤ) : leafEmb A e (-z) = (leafEmb A e z)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← leafEmb_add, add_neg_cancel, leafEmb_zero]

variable {A e T}

/-- `T` is multiplicative. -/
theorem leafT_mul
    (hT : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z))
    (g h : G) : T (g * h) = T g * T h := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  apply leafEmb_injective A e
  rw [← Matrix.mulVec_mulVec, ← hT, ← hT, ← hT]
  group

theorem leafT_one
    (hT : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z)) :
    T 1 = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  apply leafEmb_injective A e
  rw [← hT, Matrix.one_mulVec]
  group

/-- `T` is trivial on `A`, because `A` is abelian. -/
theorem leafT_of_mem
    (hT : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z))
    {a : G} (ha : a ∈ A) : T a = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  apply leafEmb_injective A e
  rw [← hT, Matrix.one_mulVec]
  have hc : ∀ x y : A, x * y = y * x := fun x y =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  have := hc ⟨a, ha⟩ (e.symm (Multiplicative.ofAdd (Pi.single i 1)))
  have := congrArg Subtype.val this
  simp only [Subgroup.coe_mul] at this
  simp only [leafEmb, this]
  group

/-- `T` as a monoid homomorphism. -/
noncomputable def leafThom
    (hT : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z)) :
    G →* Matrix (Fin k) (Fin k) ℤ where
  toFun := T
  map_one' := leafT_one hT
  map_mul' := leafT_mul hT

/-- An integer matrix as a `ℂ`-linear endomorphism of `ℂ^k`. -/
noncomputable def leafCastEnd (k : ℕ) : Matrix (Fin k) (Fin k) ℤ →+* End ℂ (Fin k → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _).toRingEquiv.toRingHom.comp
    (Int.castRingHom ℂ).mapMatrix

theorem leafCastEnd_injective (k : ℕ) : Function.Injective (leafCastEnd k) := by
  intro M N h
  have := (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _).injective h
  exact Matrix.map_injective Int.cast_injective this

/-- The representation of `G ⧸ A` on `ℂ^k` induced by `T`. -/
noncomputable def leafRhoBar [A.Normal]
    (hT : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z)) :
    G ⧸ A →* End ℂ (Fin k → ℂ) :=
  QuotientGroup.lift A ((leafCastEnd k).toMonoidHom.comp (leafThom hT)) (by
    intro a ha
    simp [MonoidHom.mem_ker, leafThom, leafT_of_mem hT ha])

/-- A product of factors `M - 1` of integer matrices vanishes once it does over `ℂ`. -/
theorem prod_sub_one_eq_zero_of_leafCastEnd {k : ℕ} (l : List (Matrix (Fin k) (Fin k) ℤ))
    (h : (l.map (fun M => leafCastEnd k M - 1)).prod = 0) :
    (l.map (fun M => M - 1)).prod = 0 := by
  apply leafCastEnd_injective k
  have hl : (l.map (fun M => M - 1)).map (leafCastEnd k)
      = l.map (fun M => leafCastEnd k M - 1) := by
    simp [List.map_map, Function.comp_def]
  rw [map_list_prod, hl, h, map_zero]

variable (A e T)

/-- The `j`-th chain subgroup of `G₀`: images under `leafEmb` of the vectors killed by every
product of `j` factors `T g - 1` with `g ∈ G₀`. -/
def leafChain (G₀ : Subgroup G) (j : ℕ) : Subgroup G₀ where
  carrier := {x | ∃ z, (x : G) = leafEmb A e z ∧ ∀ l : List G, l.length = j →
    (∀ g ∈ l, g ∈ G₀) → (l.map (fun g => T g - 1)).prod *ᵥ z = 0}
  one_mem' := ⟨0, by simp [leafEmb_zero], fun _ _ _ => Matrix.mulVec_zero _⟩
  mul_mem' := by
    rintro x y ⟨z, hz, hzl⟩ ⟨w, hw, hwl⟩
    refine ⟨z + w, by simp [Subgroup.coe_mul, hz, hw, leafEmb_add], fun l hl hl₀ => ?_⟩
    rw [Matrix.mulVec_add, hzl l hl hl₀, hwl l hl hl₀, add_zero]
  inv_mem' := by
    rintro x ⟨z, hz, hzl⟩
    refine ⟨-z, by simp [hz, leafEmb_neg], fun l hl hl₀ => ?_⟩
    rw [Matrix.mulVec_neg, hzl l hl hl₀, neg_zero]

theorem leafChain_zero (G₀ : Subgroup G) : leafChain A e T G₀ 0 = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨z, hz, hzl⟩ := hx
  have : z = 0 := by simpa using hzl [] rfl (by simp)
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [hz, this, leafEmb_zero]; rfl)

/-- `⁅N_{j+1}, G₀⁆ ≤ N_j`: the commutator of `leafEmb z` with `g` is `leafEmb (-(T g - 1) z)`. -/
theorem leafChain_step
    (hT : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z))
    (G₀ : Subgroup G) (j : ℕ) :
    ∀ x ∈ leafChain A e T G₀ (j + 1), ∀ g : G₀, ⁅x, g⁆ ∈ leafChain A e T G₀ j := by
  rintro x ⟨z, hz, hzl⟩ g
  refine ⟨-((T g - 1) *ᵥ z), ?_, fun l hl hl₀ => ?_⟩
  · have h1 : (g : G) * leafEmb A e (-z) * (g : G)⁻¹ = leafEmb A e (T g *ᵥ -z) := hT g (-z)
    rw [leafEmb_neg] at h1
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, neg_sub, sub_eq_add_neg, ← Matrix.mulVec_neg,
      leafEmb_add, ← h1, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz]
    group
  · have := hzl (l ++ [(g : G)]) (by simp [hl]) (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact hl₀ x h
      · rw [List.mem_singleton.mp h]; exact g.2)
    rw [List.map_append, List.prod_append, ← Matrix.mulVec_mulVec] at this
    rw [Matrix.mulVec_neg, neg_eq_zero]
    simpa using this

end Data

/-! ## The statement -/

set_option linter.unusedVariables false in
/-- **Rosenblatt, Theorem 4.12, linear-algebra leaf.**  If `A ◁ G` is identified with `ℤ^k`,
conjugation acts through integer matrices `T g` all of whose complex eigenvalues have modulus
`1`, and `G ⧸ A` is nilpotent, then `G` is virtually nilpotent.  (The polycyclic hypothesis is
not used.) -/
theorem isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one'
    {G : Type*} [Group G] {k : ℕ} (hpoly : MilnorWolf.IsPolycyclic G)
    (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin k → ℤ))
    (T : G → Matrix (Fin k) (Fin k) ℤ)
    (hT : ∀ (g : G) (z : Fin k → ℤ),
      g * ((e.symm (Multiplicative.ofAdd z) : A) : G) * g⁻¹
        = ((e.symm (Multiplicative.ofAdd (T g *ᵥ z)) : A) : G))
    (hnil : Group.IsNilpotent (G ⧸ A))
    (heig : ∀ (g : G) (φ : ℂ) (v : Fin k → ℂ), v ≠ 0 →
      ((T g).map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v → ‖φ‖ = 1) :
    Group.IsVirtuallyNilpotent G := by
  have hT' : ∀ (g : G) (z : Fin k → ℤ), g * leafEmb A e z * g⁻¹ = leafEmb A e (T g *ᵥ z) := hT
  set ρ := leafRhoBar hT'
  have hρ : ∀ g : G, ρ (g : G ⧸ A) = leafCastEnd k (T g) := fun g => rfl
  -- the finite eigenvalue set
  obtain ⟨S, hS, hSeig⟩ : ∃ S : Set ℂ, S.Finite ∧ ∀ γ μ, (ρ γ).HasEigenvalue μ → μ ∈ S := by
    refine ⟨_, finite_eigenvalues_of_norm_le_one k, fun γ μ hμ => ?_⟩
    induction γ using QuotientGroup.induction_on with
    | H g =>
    exact ⟨T g, fun φ v hv h => (heig g φ v hv h).le, by rwa [hρ] at hμ⟩
  -- the key theorem
  obtain ⟨Γ₀, hΓ₀, hprod⟩ := virtUnip_of_finite_eigenvalues (K := ℂ) k
    (Γ := G ⧸ A) (V := Fin k → ℂ) (by simp) ρ S hS hSeig
  set G₀ := Γ₀.comap (QuotientGroup.mk' A)
  have hG₀ : G₀.FiniteIndex := ⟨by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective A)]
    exact hΓ₀.index_ne_zero⟩
  refine ⟨G₀, ?_, hG₀⟩
  obtain ⟨c, hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  refine isNilpotent_of_lowerCentralSeries_le_chain (leafChain A e T G₀)
    (leafChain_zero A e T G₀) (leafChain_step A e T hT' G₀) (c := c) (m := k) ?_
  intro x hx
  -- `x` lies in `A`, since `G ⧸ A` has class at most `c`
  have hxA : (x : G) ∈ A := by
    have h1 : ((QuotientGroup.mk' A).comp G₀.subtype) x ∈
        (⊤ : Subgroup (G ⧸ A)).lowerCentralSeries c := by
      have := Subgroup.mem_map_of_mem ((QuotientGroup.mk' A).comp G₀.subtype) hx
      rw [Subgroup.map_lowerCentralSeries] at this
      exact Subgroup.lowerCentralSeries_mono c le_top this
    rw [hc, Subgroup.mem_bot] at h1
    simpa using h1
  -- and every product of `k` factors `T g - 1`, `g ∈ G₀`, vanishes
  refine ⟨Multiplicative.toAdd (e ⟨x, hxA⟩), by simp [leafEmb], fun l hl hl₀ => ?_⟩
  have hC := hprod (l.map (QuotientGroup.mk' A)) (by simp [hl])
    (fun γ hγ => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hγ
      exact hl₀ g hg)
  have hZ : (l.map (fun g => T g - 1)).prod = 0 := by
    have := prod_sub_one_eq_zero_of_leafCastEnd (l.map T)
      (by simpa [List.map_map, Function.comp_def, hρ] using hC)
    simpa [List.map_map, Function.comp_def] using this
  rw [hZ, Matrix.zero_mulVec]

end Rosenblatt

open Rosenblatt

theorem solution
    {G : Type*} [Group G] {k : ℕ} (hpoly : MilnorWolf.IsPolycyclic G)
    (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin k → ℤ))
    (T : G → Matrix (Fin k) (Fin k) ℤ)
    (hT : ∀ (g : G) (z : Fin k → ℤ),
      g * ((e.symm (Multiplicative.ofAdd z) : A) : G) * g⁻¹
        = ((e.symm (Multiplicative.ofAdd (T g *ᵥ z)) : A) : G))
    (hnil : Group.IsNilpotent (G ⧸ A))
    (heig : ∀ (g : G) (φ : ℂ) (v : Fin k → ℂ), v ≠ 0 →
      ((T g).map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v → ‖φ‖ = 1) :
    Group.IsVirtuallyNilpotent G :=
  Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one'
    hpoly A e T hT hnil heig
