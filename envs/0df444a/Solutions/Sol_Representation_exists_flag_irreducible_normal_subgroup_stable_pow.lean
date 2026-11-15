-- Prove2me | solution 1 for Representation.exists_flag_irreducible_normal_subgroup_stable_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T07:00:13.075054+00:00
-- url     : https://prove2.me/submissions/d08c406e-a429-4558-8ce6-b2f624f35728

import Mathlib

set_option autoImplicit false

namespace CliffordFlagSol

variable {k Γ V : Type*} [Field k] [Group Γ] [AddCommGroup V] [Module k V]

section Part1

variable (ρ : Representation k Γ V)

/-- `U` is `Γ`-stable. -/
def IsInv (U : Submodule k V) : Prop := ∀ (g : Γ), ∀ v ∈ U, ρ g v ∈ U

/-- `U` is a `Γ`-irreducible stable subspace. -/
def IsIrr (U : Submodule k V) : Prop :=
  IsInv ρ U ∧ U ≠ ⊥ ∧ ∀ U' : Submodule k V, IsInv ρ U' → U' ≤ U → U' = ⊥ ∨ U' = U

/-- `X / A` is a `Γ`-irreducible subquotient: `A < X` stable, nothing stable strictly between. -/
def IsCov (A X : Submodule k V) : Prop :=
  IsInv ρ A ∧ IsInv ρ X ∧ A < X ∧ ∀ U : Submodule k V, IsInv ρ U → A ≤ U → U ≤ X → U = A ∨ U = X

theorem isInv_bot : IsInv ρ ⊥ := fun g v hv => by
  rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero]

theorem isInv_top : IsInv ρ ⊤ := fun _ _ _ => Submodule.mem_top

/-- The image of an irreducible under a nonzero `Γ`-map is irreducible. -/
theorem isIrr_range {W : Submodule k V} (hW : IsIrr ρ W) (h : W →ₗ[k] V)
    (hh : ∀ (g : Γ) (x : W), h ⟨ρ g x, hW.1 g x x.2⟩ = ρ g (h x)) (h0 : h ≠ 0) :
    IsIrr ρ (LinearMap.range h) := by
  refine ⟨?_, ?_, fun U' hU' hle => ?_⟩
  · intro g v hv
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hv
    exact LinearMap.mem_range.2 ⟨_, hh g x⟩
  · rwa [Ne, LinearMap.range_eq_bot]
  · let P : Submodule k V := (U'.comap h).map W.subtype
    have hP : IsInv ρ P := by
      rintro g _ ⟨x, hx, rfl⟩
      refine ⟨⟨ρ g x, hW.1 g x x.2⟩, ?_, rfl⟩
      show h _ ∈ U'
      rw [hh]; exact hU' g _ hx
    rcases hW.2.2 P hP (Submodule.map_subtype_le _ _) with h1 | h1
    · left; rw [eq_bot_iff]; intro v hv
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 (hle hv)
      have hx : (x : V) ∈ P := ⟨x, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at hx
      rw [Submodule.mem_bot, show x = 0 from Subtype.ext hx, map_zero]
    · right; apply le_antisymm hle; intro v hv
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hv
      have hx : (x : V) ∈ P := by rw [h1]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← Subtype.ext hyx]; exact hy

/-! ### Bridge to `k[Γ]`-modules -/

/-- A stable `U` as a `k[Γ]`-submodule of `ρ.asModule` (same elements). -/
noncomputable def toKG (U : Submodule k V) (hU : IsInv ρ U) : Submodule (MonoidAlgebra k Γ) ρ.asModule where
  carrier := {x | ρ.asModuleEquiv x ∈ U}
  add_mem' {x y} hx hy := by
    show ρ.asModuleEquiv (x + y) ∈ U
    rw [map_add]; exact U.add_mem hx hy
  zero_mem' := by
    show ρ.asModuleEquiv 0 ∈ U
    rw [map_zero]; exact U.zero_mem
  smul_mem' r x hx := by
    show ρ.asModuleEquiv (r • x) ∈ U
    rw [Representation.asModuleEquiv_map_smul]
    exact ρ.asAlgebraHom_mem_of_forall_mem U hU _ hx r

theorem isSimpleModule_toKG {U : Submodule k V} (hU : IsIrr ρ U) :
    IsSimpleModule (MonoidAlgebra k Γ) (toKG ρ U hU.1) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨fun h => hU.2.1 ?_, fun N hN => ?_⟩
  · rw [eq_bot_iff]; intro v hv
    have hv' : ρ.asModuleEquiv.symm v ∈ toKG ρ U hU.1 := by
      show ρ.asModuleEquiv (ρ.asModuleEquiv.symm v) ∈ U
      rw [LinearEquiv.apply_symm_apply]; exact hv
    rw [h, Submodule.mem_bot] at hv'
    rw [Submodule.mem_bot, ← ρ.asModuleEquiv.apply_symm_apply v, hv', map_zero]
  · let U' : Submodule k V := (N.restrictScalars k).comap ρ.asModuleEquiv.symm.toLinearMap
    have hU' : IsInv ρ U' := fun g v hv => by
      show ρ.asModuleEquiv.symm (ρ g v) ∈ N
      rw [Representation.asModuleEquiv_symm_map_rho]; exact N.smul_mem _ hv
    have hle : U' ≤ U := fun v hv => by
      have h2 : ρ.asModuleEquiv (ρ.asModuleEquiv.symm v) ∈ U := hN.le hv
      rwa [LinearEquiv.apply_symm_apply] at h2
    rcases hU.2.2 U' hU' hle with h | h
    · rw [eq_bot_iff]; intro x hx
      have hx' : ρ.asModuleEquiv x ∈ U' := by
        show ρ.asModuleEquiv.symm (ρ.asModuleEquiv x) ∈ N
        rw [LinearEquiv.symm_apply_apply]; exact hx
      rw [h, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot, ← ρ.asModuleEquiv.symm_apply_apply x, hx', map_zero]
    · exfalso; apply hN.ne; apply le_antisymm hN.le; intro x hx
      have hx' : ρ.asModuleEquiv x ∈ U' := by rw [h]; exact hx
      have h3 : ρ.asModuleEquiv.symm (ρ.asModuleEquiv x) ∈ N := hx'
      rwa [LinearEquiv.symm_apply_apply] at h3

/-- The `k`-linear identification of a stable `U` with `toKG ρ U`. -/
noncomputable def toKGEquiv (U : Submodule k V) (hU : IsInv ρ U) : U ≃ₗ[k] toKG ρ U hU where
  toFun x := ⟨ρ.asModuleEquiv.symm x, show ρ.asModuleEquiv (ρ.asModuleEquiv.symm x) ∈ U by
    rw [LinearEquiv.apply_symm_apply]; exact x.2⟩
  invFun y := ⟨ρ.asModuleEquiv y, y.2⟩
  map_add' x y := Subtype.ext (map_add ρ.asModuleEquiv.symm _ _)
  map_smul' c x := Subtype.ext (map_smul ρ.asModuleEquiv.symm c _)
  left_inv x := Subtype.ext (ρ.asModuleEquiv.apply_symm_apply _)
  right_inv y := Subtype.ext (ρ.asModuleEquiv.symm_apply_apply _)

theorem coe_toKGEquiv_symm (U : Submodule k V) (hU : IsInv ρ U) (y : toKG ρ U hU) :
    (((toKGEquiv ρ U hU).symm y : U) : V) = ρ.asModuleEquiv y := rfl

/-- A `k[Γ]`-isomorphism of `toKG`'s is a `k`-linear `Γ`-equivariant isomorphism. -/
theorem exists_equiv_of_KG {U₁ U₂ : Submodule k V} (h₁ : IsInv ρ U₁) (h₂ : IsInv ρ U₂)
    (e : toKG ρ U₁ h₁ ≃ₗ[MonoidAlgebra k Γ] toKG ρ U₂ h₂) :
    ∃ e' : U₁ ≃ₗ[k] U₂, ∀ (g : Γ) (x : U₁), (e' ⟨ρ g x, h₁ g x x.2⟩ : V) = ρ g (e' x) := by
  refine ⟨(toKGEquiv ρ U₁ h₁).trans ((e.restrictScalars k).trans (toKGEquiv ρ U₂ h₂).symm), fun g x => ?_⟩
  have hx : toKGEquiv ρ U₁ h₁ ⟨ρ g x, h₁ g x x.2⟩ = MonoidAlgebra.of k Γ g • toKGEquiv ρ U₁ h₁ x :=
    Subtype.ext (ρ.asModuleEquiv_symm_map_rho g x)
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, hx, map_smul]
  rw [coe_toKGEquiv_symm, coe_toKGEquiv_symm, Submodule.coe_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]

/-- Two simple submodules with the same isotypic component are isomorphic. -/
theorem nonempty_equiv_of_isotypic {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {N₁ N₂ : Submodule R M}
    [IsSimpleModule R N₁] [IsSimpleModule R N₂]
    (h : isotypicComponent R M N₁ = isotypicComponent R M N₂) : Nonempty (N₂ ≃ₗ[R] N₁) := by
  have hle : N₂ ≤ isotypicComponent R M N₁ := by rw [h]; exact N₂.le_isotypicComponent
  let e1 := Submodule.comapSubtypeEquivOfLe hle
  have : IsSimpleModule R (N₂.comap (isotypicComponent R M N₁).subtype) := IsSimpleModule.congr e1
  obtain ⟨e2⟩ := IsIsotypicOfType.isotypicComponent R M N₁ (N₂.comap (isotypicComponent R M N₁).subtype)
  exact ⟨e1.symm.trans e2⟩

/-- **Isotypic pigeonhole** (K0e): among irreducible stable `U 0, U 1, …` of a finite-dimensional `V`, some
`U n`, `U m` with `n < m` are `Γ`-isomorphic. -/
theorem exists_equiv_of_irr [FiniteDimensional k V] (U : ℕ → Submodule k V) (hU : ∀ n, IsIrr ρ (U n)) :
    ∃ n m, n < m ∧ ∃ e : U n ≃ₗ[k] U m, ∀ (g : Γ) (x : U n), (e ⟨ρ g x, (hU n).1 g x x.2⟩ : V) = ρ g (e x) := by
  classical
  have : IsNoetherian (MonoidAlgebra k Γ) ρ.asModule := isNoetherian_of_tower k inferInstance
  let f : ℕ → isotypicComponents (MonoidAlgebra k Γ) ρ.asModule := fun n =>
    ⟨isotypicComponent _ _ (toKG ρ (U n) (hU n).1), toKG ρ (U n) (hU n).1, isSimpleModule_toKG ρ (hU n), rfl⟩
  obtain ⟨a, b, hab, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hf' : isotypicComponent (MonoidAlgebra k Γ) ρ.asModule (toKG ρ (U a) (hU a).1) =
      isotypicComponent (MonoidAlgebra k Γ) ρ.asModule (toKG ρ (U b) (hU b).1) := congrArg Subtype.val hf
  have := isSimpleModule_toKG ρ (hU a)
  have := isSimpleModule_toKG ρ (hU b)
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨e⟩ := nonempty_equiv_of_isotypic hf'.symm
    obtain ⟨e', he'⟩ := exists_equiv_of_KG ρ _ _ e
    exact ⟨a, b, h, e', he'⟩
  · obtain ⟨e⟩ := nonempty_equiv_of_isotypic hf'
    obtain ⟨e', he'⟩ := exists_equiv_of_KG ρ _ _ e
    exact ⟨b, a, h, e', he'⟩


end Part1

section Part2


/-- `Φ` normalises `ρ` along `φ`: `Φ (ρ γ v) = ρ (φ γ) (Φ v)`. -/
def Normalizes (ρ : Representation k Γ V) (Φ : V ≃ₗ[k] V) (φ : MulAut Γ) : Prop :=
  ∀ (g : Γ) (v : V), Φ (ρ g v) = ρ (φ g) (Φ v)

variable {ρ : Representation k Γ V}

theorem Normalizes.symm {Φ : V ≃ₗ[k] V} {φ : MulAut Γ} (h : Normalizes ρ Φ φ) :
    ∀ (g : Γ) (v : V), Φ.symm (ρ g v) = ρ (φ.symm g) (Φ.symm v) := by
  intro g v
  apply Φ.injective
  rw [h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem Normalizes.mul {Φ Ψ : V ≃ₗ[k] V} {φ ψ : MulAut Γ} (h₁ : Normalizes ρ Φ φ) (h₂ : Normalizes ρ Ψ ψ) :
    Normalizes ρ (Φ * Ψ) (φ * ψ) := fun g v => by
  show Φ (Ψ (ρ g v)) = ρ (φ (ψ g)) (Φ (Ψ v))
  rw [h₂, h₁]

theorem Normalizes.pow {Φ : V ≃ₗ[k] V} {φ : MulAut Γ} (h : Normalizes ρ Φ φ) (n : ℕ) :
    Normalizes ρ (Φ ^ n) (φ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact fun g v => rfl
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem stable_pow {Φ : V ≃ₗ[k] V} {A : Submodule k V} (h : ∀ v ∈ A, Φ v ∈ A) (n : ℕ) :
    ∀ v ∈ A, (Φ ^ n) v ∈ A := by
  induction n with
  | zero => intro v hv; rw [pow_zero]; exact hv
  | succ n ih => intro v hv; rw [pow_succ]; exact ih _ (h v hv)

theorem Normalizes.isInv_map {Φ : V ≃ₗ[k] V} {φ : MulAut Γ} (h : Normalizes ρ Φ φ) {U : Submodule k V}
    (hU : IsInv ρ U) : IsInv ρ (U.map (Φ : V →ₗ[k] V)) := by
  rintro g _ ⟨u, hu, rfl⟩
  refine ⟨ρ (φ.symm g) u, hU _ u hu, ?_⟩
  show Φ (ρ (φ.symm g) u) = ρ g (Φ u)
  rw [h, MulEquiv.apply_symm_apply]

theorem Normalizes.isIrr_map {Φ : V ≃ₗ[k] V} {φ : MulAut Γ} (h : Normalizes ρ Φ φ) {U : Submodule k V}
    (hU : IsIrr ρ U) : IsIrr ρ (U.map (Φ : V →ₗ[k] V)) := by
  have hcm := Submodule.comap_map_eq_of_injective (f := (Φ : V →ₗ[k] V)) Φ.injective U
  refine ⟨h.isInv_map hU.1, fun h0 => hU.2.1 ?_, fun U' hU' hle => ?_⟩
  · rw [h0, Submodule.comap_bot, LinearEquiv.ker] at hcm; exact hcm.symm
  · have hinv : IsInv ρ (U'.comap (Φ : V →ₗ[k] V)) := fun g v hv => by
      show Φ (ρ g v) ∈ U'
      rw [h]; exact hU' _ _ hv
    have hle' : U'.comap (Φ : V →ₗ[k] V) ≤ U := hcm ▸ Submodule.comap_mono hle
    have hmc := Submodule.map_comap_eq_of_surjective (f := (Φ : V →ₗ[k] V)) Φ.surjective U'
    rcases hU.2.2 _ hinv hle' with h1 | h1
    · left; rw [← hmc, h1, Submodule.map_bot]
    · right; rw [← hmc, h1]

/-- A nonzero finite-dimensional representation has an irreducible stable subspace. -/
theorem exists_isIrr (ρ : Representation k Γ V) [FiniteDimensional k V] [Nontrivial V] : ∃ W, IsIrr ρ W := by
  classical
  have hex : ∃ n, ∃ U : Submodule k V, IsInv ρ U ∧ U ≠ ⊥ ∧ Module.finrank k U = n :=
    ⟨_, ⊤, isInv_top ρ, top_ne_bot, rfl⟩
  obtain ⟨U, hU, hU0, hUn⟩ := Nat.find_spec hex
  refine ⟨U, hU, hU0, fun U' hU' hle => ?_⟩
  by_contra hne
  rw [not_or] at hne
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne.2)
  rw [hUn] at hlt
  exact Nat.find_min hex hlt ⟨U', hU', hne.1, rfl⟩

/-- **Twisted intertwiner** (K0e): `W` irreducible, `e : W ≅ Ψ W` over `Γ` ⇒ a `Ψ`-stable irreducible exists. -/
theorem exists_isIrr_stable_of_equiv [IsAlgClosed k] [FiniteDimensional k V] {Ψ : V ≃ₗ[k] V} {ψ : MulAut Γ}
    (hΨ : Normalizes ρ Ψ ψ) {W : Submodule k V} (hW : IsIrr ρ W) (e : W ≃ₗ[k] W.map (Ψ : V →ₗ[k] V))
    (he : ∀ (g : Γ) (x : W), (e ⟨ρ g x, hW.1 g x x.2⟩ : V) = ρ g (e x)) :
    ∃ X : Submodule k V, IsIrr ρ X ∧ ∀ v ∈ X, Ψ v ∈ X := by
  have hD : ∀ x ∈ W.map (Ψ : V →ₗ[k] V), (Ψ.symm : V →ₗ[k] V) x ∈ W := by
    rintro _ ⟨u, hu, rfl⟩
    show Ψ.symm (Ψ u) ∈ W
    rw [LinearEquiv.symm_apply_apply]; exact hu
  let D : W →ₗ[k] W := ((Ψ.symm : V →ₗ[k] V).restrict hD) ∘ₗ (e : W →ₗ[k] W.map (Ψ : V →ₗ[k] V))
  have hDg : ∀ (g : Γ) (x : W), D ⟨ρ g x, hW.1 g x x.2⟩ = ⟨ρ (ψ.symm g) (D x), hW.1 _ _ (D x).2⟩ := by
    intro g x
    apply Subtype.ext
    show Ψ.symm (e ⟨ρ g x, hW.1 g x x.2⟩ : V) = ρ (ψ.symm g) (Ψ.symm (e x))
    rw [he, hΨ.symm]
  let H : Submodule k (W →ₗ[k] V) :=
    { carrier := {h | ∀ (g : Γ) (x : W), h ⟨ρ g x, hW.1 g x x.2⟩ = ρ g (h x)}
      add_mem' := fun {a b} ha hb g x => by
        simp only [LinearMap.add_apply, map_add]; rw [ha g x, hb g x]
      zero_mem' := fun g x => by simp
      smul_mem' := fun c a ha g x => by
        simp only [LinearMap.smul_apply, map_smul]; rw [ha g x] }
  have hT : ∀ h ∈ H, (Ψ : V →ₗ[k] V) ∘ₗ h ∘ₗ D ∈ H := by
    intro h hh g x
    show Ψ (h (D ⟨ρ g x, hW.1 g x x.2⟩)) = ρ g (Ψ (h (D x)))
    rw [hDg, hh, hΨ, MulEquiv.apply_symm_apply]
  let T : Module.End k H :=
    { toFun := fun h => ⟨(Ψ : V →ₗ[k] V) ∘ₗ h.1 ∘ₗ D, hT h.1 h.2⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun x => by simp)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun x => by simp) }
  have hsub : W.subtype ∈ H := fun g x => rfl
  obtain ⟨w0, hw0, hw0ne⟩ := (Submodule.ne_bot_iff W).1 hW.2.1
  have : Nontrivial H := ⟨⟨⟨W.subtype, hsub⟩, 0, fun h0 => hw0ne (by
    have := congrArg (fun F : H => (F : W →ₗ[k] V) ⟨w0, hw0⟩) h0
    simpa using this)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨h0, hh0⟩ := hc.exists_hasEigenvector
  have hTh0 : ∀ x : W, Ψ (h0.1 (D x)) = c • h0.1 x := fun x =>
    congrArg (fun F : H => (F : W →ₗ[k] V) x) hh0.apply_eq_smul
  have hne : (h0.1 : W →ₗ[k] V) ≠ 0 := fun h => hh0.2 (Subtype.ext h)
  refine ⟨LinearMap.range h0.1, isIrr_range ρ hW h0.1 h0.2 hne, fun v hv => ?_⟩
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hv
  let x : W := e.symm ⟨Ψ w, Submodule.mem_map_of_mem w.2⟩
  have hDx : D x = w := by
    apply Subtype.ext
    show Ψ.symm (e (e.symm ⟨Ψ w, Submodule.mem_map_of_mem w.2⟩) : V) = w
    rw [LinearEquiv.apply_symm_apply]
    exact Ψ.symm_apply_apply w
  rw [← hDx, hTh0]
  exact LinearMap.mem_range.2 ⟨c • x, map_smul _ _ _⟩

/-- **Clifford step** (K0e): over `k` algebraically closed, some `Φ ^ d` (`d ≥ 1`) stabilises a `Γ`-irreducible
stable subspace of a nonzero finite-dimensional `V`. -/
theorem exists_isIrr_stable [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] {Φ : V ≃ₗ[k] V}
    {φ : MulAut Γ} (hΦ : Normalizes ρ Φ φ) :
    ∃ d, 0 < d ∧ ∃ X : Submodule k V, IsIrr ρ X ∧ ∀ v ∈ X, (Φ ^ d) v ∈ X := by
  obtain ⟨W, hW⟩ := exists_isIrr ρ
  obtain ⟨n, m, hnm, e, he⟩ := exists_equiv_of_irr ρ (fun n => W.map ((Φ ^ n : V ≃ₗ[k] V) : V →ₗ[k] V))
    (fun n => (hΦ.pow n).isIrr_map hW)
  have hm : W.map ((Φ ^ m : V ≃ₗ[k] V) : V →ₗ[k] V) = (W.map ((Φ ^ n : V ≃ₗ[k] V) : V →ₗ[k] V)).map
      ((Φ ^ (m - n) : V ≃ₗ[k] V) : V →ₗ[k] V) := by
    rw [← Submodule.map_comp]
    congr 1
    ext v
    show (Φ ^ m) v = (Φ ^ (m - n) * Φ ^ n) v
    rw [pow_sub_mul_pow Φ hnm.le]
  obtain ⟨X, hX, hXs⟩ := exists_isIrr_stable_of_equiv (hΦ.pow (m - n)) ((hΦ.pow n).isIrr_map hW)
    (e.trans (LinearEquiv.ofEq _ _ hm)) (fun g x => by
      rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, he, LinearEquiv.trans_apply,
        LinearEquiv.coe_ofEq_apply])
  exact ⟨m - n, Nat.sub_pos_of_lt hnm, X, hX, hXs⟩

end Part2

section Part3

variable {ρ : Representation k Γ V}

/-- The representation on `V ⧸ A`, `A` stable. -/
noncomputable def quotRep (A : Submodule k V) (hA : IsInv ρ A) : Representation k Γ (V ⧸ A) where
  toFun g := A.mapQ A (ρ g) (fun v hv => hA g v hv)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

theorem quotRep_mk (A : Submodule k V) (hA : IsInv ρ A) (g : Γ) (v : V) :
    quotRep A hA g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

theorem map_eq_of_stable [FiniteDimensional k V] {Φ : V ≃ₗ[k] V} {A : Submodule k V} (h : ∀ v ∈ A, Φ v ∈ A) :
    A.map (Φ : V →ₗ[k] V) = A :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact h v hv) (LinearEquiv.finrank_map_eq Φ A)

/-- `Φ` on `V ⧸ A`. -/
noncomputable def quotΦ [FiniteDimensional k V] {Φ : V ≃ₗ[k] V} {A : Submodule k V} (h : ∀ v ∈ A, Φ v ∈ A) :
    (V ⧸ A) ≃ₗ[k] (V ⧸ A) :=
  Submodule.Quotient.equiv A A Φ (map_eq_of_stable h)

theorem quotΦ_mk [FiniteDimensional k V] {Φ : V ≃ₗ[k] V} {A : Submodule k V} (h : ∀ v ∈ A, Φ v ∈ A) (v : V) :
    quotΦ h (Submodule.Quotient.mk v) = Submodule.Quotient.mk (Φ v) := rfl

theorem quotΦ_pow_mk [FiniteDimensional k V] {Φ : V ≃ₗ[k] V} {A : Submodule k V} (h : ∀ v ∈ A, Φ v ∈ A)
    (n : ℕ) (v : V) : (quotΦ h ^ n) (Submodule.Quotient.mk v) = Submodule.Quotient.mk ((Φ ^ n) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, LinearEquiv.mul_apply, quotΦ_mk, ih, LinearEquiv.mul_apply]

theorem Normalizes.quot [FiniteDimensional k V] {Φ : V ≃ₗ[k] V} {φ : MulAut Γ} (hΦ : Normalizes ρ Φ φ)
    {A : Submodule k V} (hA : IsInv ρ A) (h : ∀ v ∈ A, Φ v ∈ A) : Normalizes (quotRep A hA) (quotΦ h) φ := by
  intro g v
  induction v using Submodule.Quotient.induction_on with
  | H v => rw [quotRep_mk, quotΦ_mk, quotΦ_mk, quotRep_mk, hΦ]

/-- An irreducible stable subspace of `V ⧸ A` pulls back to a `Γ`-irreducible step `A ⋖ X`. -/
theorem isCov_comap {A : Submodule k V} (hA : IsInv ρ A) {X : Submodule k (V ⧸ A)} (hX : IsIrr (quotRep A hA) X) :
    IsCov ρ A (X.comap A.mkQ) := by
  refine ⟨hA, fun g v hv => hX.1 g _ hv, lt_of_le_of_ne (fun v hv => ?_) (fun h => hX.2.1 ?_),
    fun U hU hAU hUX => ?_⟩
  · show A.mkQ v ∈ X
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).2 hv]; exact X.zero_mem
  · rw [← Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective A) X, ← h, Submodule.mkQ_map_self]
  · have hU' : IsInv (quotRep A hA) (U.map A.mkQ) := by
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨ρ g u, hU g u hu, rfl⟩
    rcases hX.2.2 _ hU' (Submodule.map_le_iff_le_comap.2 hUX) with h | h
    · left
      refine le_antisymm (fun u hu => ?_) hAU
      have : A.mkQ u ∈ U.map A.mkQ := Submodule.mem_map_of_mem hu
      rw [h, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    · right
      rw [← h, Submodule.comap_map_mkQ, sup_eq_right.2 hAU]

/-- The chain from a stable `A` (also `Φ`-stable) up to `⊤`, by induction on `dim V ⧸ A`. -/
theorem exists_chain [IsAlgClosed k] [FiniteDimensional k V] (n : ℕ) :
    ∀ (Φ : V ≃ₗ[k] V) (φ : MulAut Γ) (A : Submodule k V), Normalizes ρ Φ φ → IsInv ρ A → (∀ v ∈ A, Φ v ∈ A) →
      Module.finrank k (V ⧸ A) = n → ∃ d, 0 < d ∧ ∃ r, ∃ F : ℕ → Submodule k V, F 0 = A ∧ F r = ⊤ ∧
        (∀ i < r, IsCov ρ (F i) (F (i + 1))) ∧ ∀ i ≤ r, ∀ v ∈ F i, (Φ ^ d) v ∈ F i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Φ φ A hΦ hA hAΦ hn
  by_cases htop : A = ⊤
  · exact ⟨1, one_pos, 0, fun _ => ⊤, htop.symm, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ _ _ => Submodule.mem_top⟩
  obtain ⟨v₀, -, hv₀⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 htop)
  have : Nontrivial (V ⧸ A) := nontrivial_of_ne (Submodule.Quotient.mk v₀) 0
    (by rwa [Ne, Submodule.Quotient.mk_eq_zero])
  obtain ⟨d₁, hd₁, X, hX, hXs⟩ := exists_isIrr_stable (hΦ.quot hA hAΦ)
  have hcov := isCov_comap hA hX
  have hstab : ∀ v ∈ X.comap A.mkQ, (Φ ^ d₁) v ∈ X.comap A.mkQ := fun v hv => by
    show A.mkQ ((Φ ^ d₁) v) ∈ X
    rw [Submodule.mkQ_apply, ← quotΦ_pow_mk hAΦ]; exact hXs _ hv
  have hlt : Module.finrank k (V ⧸ X.comap A.mkQ) < n := by
    have h1 := Submodule.finrank_quotient_add_finrank A
    have h2 := Submodule.finrank_quotient_add_finrank (X.comap A.mkQ)
    have h3 := Submodule.finrank_lt_finrank_of_lt hcov.2.2.1
    omega
  obtain ⟨d₂, hd₂, r, F, hF0, hFr, hFc, hFs⟩ :=
    ih _ hlt (Φ ^ d₁) (φ ^ d₁) _ (hΦ.pow d₁) hcov.2.1 hstab rfl
  refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, r + 1, fun | 0 => A | i + 1 => F i, rfl, hFr, fun i hi => ?_,
    fun i hi v hv => ?_⟩
  · rcases i with _ | i
    · show IsCov ρ A (F 0)
      rw [hF0]; exact hcov
    · exact hFc i (by omega)
  · rcases i with _ | i
    · exact stable_pow hAΦ _ v hv
    · rw [pow_mul]; exact hFs i (by omega) v hv

/-- **Clifford flag** (K0e): `d ≥ 1` and a `Γ`- and `Φ ^ d`-stable flag with `Γ`-irreducible graded pieces. -/
theorem exists_flag [IsAlgClosed k] [FiniteDimensional k V] {Φ : V ≃ₗ[k] V} {φ : MulAut Γ}
    (hΦ : Normalizes ρ Φ φ) : ∃ d, 0 < d ∧ ∃ r, ∃ F : ℕ → Submodule k V, F 0 = ⊥ ∧ F r = ⊤ ∧
      (∀ i < r, IsCov ρ (F i) (F (i + 1))) ∧ ∀ i ≤ r, ∀ v ∈ F i, (Φ ^ d) v ∈ F i :=
  exists_chain _ Φ φ ⊥ hΦ (isInv_bot ρ) (fun v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero]) rfl

section Weil

variable {W : Type*} [Group W] (σ : Representation k W V)

/-- `σ f` as a linear automorphism. -/
noncomputable def frobEquiv (f : W) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (σ f) (σ f⁻¹) (LinearMap.ext fun v => σ.self_inv_apply f v)
    (LinearMap.ext fun v => σ.inv_self_apply f v)

theorem frobEquiv_pow_apply (f : W) (n : ℕ) (v : V) : (frobEquiv σ f ^ n) v = σ (f ^ n) v := by
  induction n generalizing v with
  | zero => rw [pow_zero, pow_zero, map_one]; rfl
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]; rfl

theorem normalizes_frobEquiv (Γ' : Subgroup W) [Γ'.Normal] (f : W) :
    Normalizes (σ.comp Γ'.subtype) (frobEquiv σ f) (MulAut.conjNormal f) := by
  intro g v
  show σ f (σ g v) = σ ((MulAut.conjNormal f g : Γ') : W) (σ f v)
  rw [MulAut.conjNormal_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    inv_mul_cancel_right]

/-- **Clifford flag, Weil-group form** (K0e): `Γ ◁ W`, `f ∈ W`. -/
theorem exists_flag_weil [IsAlgClosed k] [FiniteDimensional k V] (Γ' : Subgroup W) [Γ'.Normal] (f : W) :
    ∃ d, 0 < d ∧ ∃ r, ∃ F : ℕ → Submodule k V, F 0 = ⊥ ∧ F r = ⊤ ∧
      (∀ i < r, IsCov (σ.comp Γ'.subtype) (F i) (F (i + 1))) ∧ ∀ i ≤ r, ∀ v ∈ F i, σ (f ^ d) v ∈ F i := by
  obtain ⟨d, hd, r, F, h0, hr, hc, hs⟩ := exists_flag (normalizes_frobEquiv σ Γ' f)
  exact ⟨d, hd, r, F, h0, hr, hc, fun i hi v hv => by rw [← frobEquiv_pow_apply]; exact hs i hi v hv⟩

end Weil

end Part3

end CliffordFlagSol

open CliffordFlagSol in
theorem solution
    {k W V : Type*} [Field k] [IsAlgClosed k] [Group W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σ : Representation k W V) (Γ : Subgroup W) [Γ.Normal] (f : W) :
    ∃ d : ℕ, 0 < d ∧ ∃ r : ℕ, ∃ F : ℕ → Submodule k V, F 0 = ⊥ ∧ F r = ⊤ ∧
      (∀ i ≤ r, ∀ g ∈ Γ, ∀ v ∈ F i, σ g v ∈ F i) ∧
      (∀ i ≤ r, ∀ v ∈ F i, σ (f ^ d) v ∈ F i) ∧
      ∀ i < r, F i < F (i + 1) ∧
        ∀ U : Submodule k V, (∀ g ∈ Γ, ∀ v ∈ U, σ g v ∈ U) → F i ≤ U → U ≤ F (i + 1) →
          U = F i ∨ U = F (i + 1) := by
  obtain ⟨d, hd, r, F, h0, hr, hc, hs⟩ := CliffordFlagSol.exists_flag_weil σ Γ f
  have hinv : ∀ U : Submodule k V, IsInv (σ.comp Γ.subtype) U → ∀ g ∈ Γ, ∀ v ∈ U, σ g v ∈ U :=
    fun U hU g hg v hv => hU ⟨g, hg⟩ v hv
  refine ⟨d, hd, r, F, h0, hr, fun i hi g hg v hv => ?_, hs, fun i hi => ⟨(hc i hi).2.2.1, fun U hU h1 h2 => ?_⟩⟩
  · rcases Nat.lt_or_ge i r with h | h
    · exact hinv _ (hc i h).1 g hg v hv
    · rw [show i = r by omega, hr]; exact Submodule.mem_top
  · exact (hc i hi).2.2.2 U (fun g v hv => hU g.1 g.2 v hv) h1 h2
