-- Prove2me | solution 1 for ValuationSubring.exists_kummer_generator_of_additive_inertia_character
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0174f29a-19e7-5018-a921-c9a5fc13f062

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_kummer_generator_of_additive_inertia_character

set_option autoImplicit false

open groupCohomology groupCohomology.Kummer
open scoped Pointwise

local instance c3a_isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance c3a_isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance c3a_isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace C3aAux

section Clopen

variable {Γ : Type} [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ]

theorem isOpen_of_mul_mem {T : Set Γ} (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (h : ∀ t ∈ T, ∀ u ∈ U, t * u ∈ T) : IsOpen T := by
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  refine ⟨(fun x => t * x) '' (U : Set Γ), ?_, isOpenMap_mul_left t _ hU, ⟨1, U.one_mem, mul_one t⟩⟩
  rintro _ ⟨u, hu, rfl⟩
  exact h t ht u hu

theorem isClosed_of_mul_mem {T : Set Γ} (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (h : ∀ t ∈ T, ∀ u ∈ U, t * u ∈ T) : IsClosed T := by
  rw [← isOpen_compl_iff]
  refine isOpen_of_mul_mem U hU fun t ht u hu htu => ht ?_
  have := h (t * u) htu u⁻¹ (U.inv_mem hu)
  rwa [mul_inv_cancel_right] at this

end Clopen

section Inertia

theorem isOpen_fixingSubgroup_adjoin (a : AlgebraicClosure ℚ) :
    IsOpen ((IntermediateField.adjoin ℚ ({a} : Set (AlgebraicClosure ℚ))).fixingSubgroup :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({a} : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  exact IntermediateField.fixingSubgroup_isOpen _

theorem apply_eq_of_mem_fixingSubgroup_adjoin (a : AlgebraicClosure ℚ)
    {u : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hu : u ∈ (IntermediateField.adjoin ℚ ({a} : Set (AlgebraicClosure ℚ))).fixingSubgroup) : u a = a :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp hu a (IntermediateField.mem_adjoin_simple_self ℚ a)

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ A.inertiaSubgroupIn ℚ ↔ σ • A = A ∧ ∀ a ∈ A, σ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨MulAction.mem_stabilizer_iff.mp d.2, fun a ha => ?_⟩
    have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ)
        (IsLocalRing.ResidueField A) d = 1 := hd
    have h2 : d • IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨a, ha⟩ :=
      DFunLike.congr_fun h1 (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul] at h2
    have h3 : (d • (⟨a, ha⟩ : A)) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.mp h2
    have h4 := ValuationSubring.coe_mem_nonunits_iff.mpr h3
    exact h4
  · rintro ⟨hD, h⟩
    let d : A.decompositionSubgroup ℚ := ⟨σ, MulAction.mem_stabilizer_iff.mpr hD⟩
    refine Subgroup.mem_map.mpr ⟨d, ?_, rfl⟩
    show MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (IsLocalRing.ResidueField A) d = 1
    refine RingEquiv.ext fun r => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    show d • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul]
    exact Ideal.Quotient.eq.mpr (ValuationSubring.coe_mem_nonunits_iff.mp (h a a.2))

theorem mem_smul_iff (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (y : AlgebraicClosure ℚ) :
    y ∈ σ • A ↔ σ⁻¹ y ∈ A := by
  conv_lhs => rw [← smul_inv_smul σ y]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

theorem isClosed_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsClosed ((A.inertiaSubgroupIn ℚ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  have hset : ((A.inertiaSubgroupIn ℚ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) =
      {σ | σ • A = A} ∩ ⋂ a : A, {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
        σ (a : AlgebraicClosure ℚ) - a ∈ A.nonunits} := by
    ext σ
    rw [SetLike.mem_coe, mem_inertiaSubgroupIn_iff]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
  rw [hset]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => ?_)
  ·
    have hstab : {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ • A = A} =
        ⋂ y : AlgebraicClosure ℚ, {σ | σ⁻¹ y ∈ A ↔ y ∈ A} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [SetLike.ext_iff]
      exact forall_congr' fun y => by rw [mem_smul_iff]
    rw [hstab]
    refine isClosed_iInter fun y => ?_

    have hW : ∀ t ∈ {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | τ y ∈ A},
        ∀ u ∈ (IntermediateField.adjoin ℚ ({y} : Set (AlgebraicClosure ℚ))).fixingSubgroup,
        t * u ∈ {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | τ y ∈ A} := by
      intro t ht u hu
      simp only [Set.mem_setOf_eq, AlgEquiv.mul_apply] at ht ⊢
      rwa [apply_eq_of_mem_fixingSubgroup_adjoin y hu]
    have hWo : IsOpen {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | τ y ∈ A} :=
      isOpen_of_mul_mem _ (isOpen_fixingSubgroup_adjoin y) hW
    have hWc : IsClosed {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | τ y ∈ A} :=
      isClosed_of_mul_mem _ (isOpen_fixingSubgroup_adjoin y) hW
    have hV : {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ⁻¹ y ∈ A} =
        (fun σ => σ⁻¹) ⁻¹' {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | τ y ∈ A} := rfl
    by_cases hy : y ∈ A
    · have : {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ⁻¹ y ∈ A ↔ y ∈ A} =
          {σ | σ⁻¹ y ∈ A} := by
        ext σ; simp only [Set.mem_setOf_eq, hy, iff_true]
      rw [this, hV]
      exact hWc.preimage continuous_inv
    · have : {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ⁻¹ y ∈ A ↔ y ∈ A} =
          {σ | σ⁻¹ y ∈ A}ᶜ := by
        ext σ; simp only [Set.mem_setOf_eq, hy, iff_false, Set.mem_compl_iff]
      rw [this, hV, isClosed_compl_iff]
      exact hWo.preimage continuous_inv
  ·
    refine isClosed_of_mul_mem _ (isOpen_fixingSubgroup_adjoin (a : AlgebraicClosure ℚ)) ?_
    intro t ht u hu
    simp only [Set.mem_setOf_eq, AlgEquiv.mul_apply] at ht ⊢
    rwa [apply_eq_of_mem_fixingSubgroup_adjoin (a : AlgebraicClosure ℚ) hu]

theorem fixingSubgroup_fixedField_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)).fixingSubgroup = A.inertiaSubgroupIn ℚ :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨A.inertiaSubgroupIn ℚ, isClosed_inertiaSubgroupIn A⟩

end Inertia

theorem fixes_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (g : L ≃ₐ[K] L)
    (S : Set L) (hS : ∀ s ∈ S, g s = s) : ∀ x ∈ IntermediateField.adjoin K S, g x = x := by
  intro x hx
  have hle : IntermediateField.adjoin K S ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
    refine IntermediateField.adjoin_le_iff.mpr fun s hs => ?_
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h : Subgroup.zpowers g ≤ MulAction.stabilizer (L ≃ₐ[K] L) s :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hS s hs)
    exact h hf
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) g (Subgroup.mem_zpowers g)

theorem pow_val_eq {M : Type} [Monoid M] {ζ : M} {m : ℕ} [NeZero m] (hζ : ζ ^ m = 1)
    (u : ZMod m) (k : ℕ) (h : (k : ZMod m) = u) : ζ ^ u.val = ζ ^ k := by
  rw [← h, ZMod.val_natCast, ← pow_eq_pow_mod k hζ]

end C3aAux

open C3aAux in
theorem solution
    (p : ℕ) (hp : p.Prime) (N n : ℕ) (hn : n ≤ N)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod (p ^ n))
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → χ (τ * s) = χ τ)
    (hadd : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) → χ (τ * τ') = χ τ + χ τ') :
    ∃ x γ : AlgebraicClosure ℚ, x ≠ 0 ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → σ ξ = ξ) → σ x = x) ∧ γ ^ p ^ n = x ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : ℕ, τ γ = (ζ ^ p ^ (N - n)) ^ k * γ → χ τ = k := by
  classical
  have _hP := hP
  haveI hpn0 : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI hpN0 : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩

  set I := P.inertiaSubgroupIn ℚ with hIdef
  let k₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField I
  have hfix : k₀.fixingSubgroup = I := fixingSubgroup_fixedField_inertiaSubgroupIn P
  haveI : IsGalois (↥k₀) (AlgebraicClosure ℚ) := IsGalois.tower_top_of_isGalois ℚ (↥k₀) (AlgebraicClosure ℚ)

  let KN : IntermediateField (↥k₀) (AlgebraicClosure ℚ) := IntermediateField.adjoin (↥k₀) {ζ}
  have hζKN : ζ ∈ KN := IntermediateField.mem_adjoin_simple_self (↥k₀) ζ
  haveI : FiniteDimensional (↥k₀) KN :=
    IntermediateField.adjoin.finiteDimensional
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ζ).isIntegral.tower_top)
  have hζn : IsPrimitiveRoot (ζ ^ p ^ (N - n)) (p ^ n) :=
    hζ.pow (pow_pos hp.pos N) (by rw [← pow_add, Nat.sub_add_cancel hn])
  have hζn1 : (ζ ^ p ^ (N - n)) ^ p ^ n = 1 := hζn.pow_eq_one
  let ζu : (AlgebraicClosure ℚ)ˣ := (hζn.isUnit (NeZero.ne _)).unit
  have hζu : (ζu : AlgebraicClosure ℚ) = ζ ^ p ^ (N - n) := (hζn.isUnit (NeZero.ne _)).unit_spec
  have hζu1 : ζu ^ p ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζn1, Units.val_one])

  have hroots : ∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → ∃ i : ℕ, ζ ^ i = ξ := fun ξ hξ => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact ⟨i, hi⟩

  let ρ : KN.fixingSubgroup → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := fun σ =>
    (σ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ).restrictScalars ℚ
  have hρ_apply : ∀ (σ : KN.fixingSubgroup) (y : AlgebraicClosure ℚ),
      ρ σ y = (σ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ) y := fun _ _ => rfl
  have hρI : ∀ σ : KN.fixingSubgroup, ρ σ ∈ I := by
    intro σ
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rw [hρ_apply]
    exact (σ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ).commutes ⟨y, hy⟩
  have hρμ : ∀ (σ : KN.fixingSubgroup) (ξ : AlgebraicClosure ℚ), ξ ^ p ^ N = 1 → ρ σ ξ = ξ := by
    intro σ ξ hξ
    obtain ⟨i, rfl⟩ := hroots ξ hξ
    rw [map_pow, hρ_apply]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp σ.2 ζ hζKN
  have hρmul : ∀ σ τ : KN.fixingSubgroup, ρ (σ * τ) = ρ σ * ρ τ := fun _ _ => AlgEquiv.ext fun _ => rfl
  have hχ1 : χ 1 = 0 := by
    have h := hadd 1 I.one_mem 1 I.one_mem (fun ξ _ => rfl) (fun ξ _ => rfl)
    rw [mul_one] at h
    exact add_left_cancel (a := χ 1) (h.symm.trans (add_zero _).symm)

  let χ' : KN.fixingSubgroup →* (AlgebraicClosure ℚ)ˣ :=
    { toFun := fun σ => ζu ^ (χ (ρ σ)).val
      map_one' := by
        have h1 : ρ 1 = 1 := AlgEquiv.ext fun _ => rfl
        show ζu ^ (χ (ρ 1)).val = 1
        rw [h1, hχ1, ZMod.val_zero, pow_zero]
      map_mul' := fun σ τ => by
        show ζu ^ (χ (ρ (σ * τ))).val = ζu ^ (χ (ρ σ)).val * ζu ^ (χ (ρ τ)).val
        rw [hρmul, hadd _ (hρI σ) _ (hρI τ) (hρμ σ) (hρμ τ), ← pow_add]
        exact pow_val_eq hζu1 _ _ (by rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]) }
  have hχ'_apply : ∀ σ : KN.fixingSubgroup, (χ' σ : AlgebraicClosure ℚ) =
      (ζ ^ p ^ (N - n)) ^ (χ (ρ σ)).val := fun σ => by
    show ((ζu ^ (χ (ρ σ)).val : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
    rw [Units.val_pow_eq_pow_val, hζu]
  have hχ'p : ∀ σ : KN.fixingSubgroup, χ' σ ^ p ^ n = 1 := fun σ => by
    show (ζu ^ (χ (ρ σ)).val) ^ p ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, hζu1, one_pow]
  have hμ : ∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ n = 1 → ξ ∈ KN := by
    intro ξ hξ
    obtain ⟨i, -, rfl⟩ := hζn.eq_pow_of_pow_eq_one hξ
    rw [← pow_mul]
    exact pow_mem hζKN _

  obtain ⟨F, hFfd, hFlev⟩ := hlev
  have hlc : ∃ L : IntermediateField (↥k₀) (AlgebraicClosure ℚ), FiniteDimensional (↥k₀) L ∧
      ∀ τ : KN.fixingSubgroup, (τ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ) ∈ L.fixingSubgroup →
        χ' τ = 1 := by
    haveI := hFfd
    obtain ⟨T, hT⟩ : F.FG :=
      F.fg_of_fg_toSubalgebra (Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hFfd))
    refine ⟨IntermediateField.adjoin (↥k₀) (↑T : Set (AlgebraicClosure ℚ)), ?_, ?_⟩
    · haveI : Finite (↑T : Set (AlgebraicClosure ℚ)) := T.finite_toSet.to_subtype
      exact IntermediateField.finiteDimensional_adjoin fun x _ =>
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral.tower_top
    · intro τ hτ
      have hτT : ∀ x ∈ (↑T : Set (AlgebraicClosure ℚ)), ρ τ x = x := fun x hx => by
        rw [hρ_apply]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.subset_adjoin _ _ hx)
      have hτF : ρ τ ∈ F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        rw [← hT] at hx
        exact fixes_adjoin (ρ τ) _ hτT x hx
      have h0 : χ (ρ τ) = 0 := by
        have := hFlev 1 I.one_mem (ρ τ) (hρI τ) hτF
        rw [one_mul, hχ1] at this
        exact this
      apply Units.ext
      rw [hχ'_apply, h0, ZMod.val_zero, pow_zero, Units.val_one]

  obtain ⟨a, α, haα, hχ'⟩ :=
    exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup KN hμ χ' hχ'p hlc
  refine ⟨((a : ↥KN) : AlgebraicClosure ℚ), (α : AlgebraicClosure ℚ), ?_, ?_, ?_, ?_⟩
  ·
    intro h0
    exact a.ne_zero ((ZeroMemClass.coe_eq_zero).mp h0)
  ·
    intro σ hσ hσμ
    have hσk : σ ∈ k₀.fixingSubgroup := by rw [hfix]; exact hσ
    let φ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ :=
      IntermediateField.fixingSubgroupEquiv k₀ ⟨σ, hσk⟩
    have hφ : ∀ y, φ y = σ y := fun _ => rfl
    have hφζ : φ ζ = ζ := by rw [hφ]; exact hσμ ζ hζ.pow_eq_one
    have := fixes_adjoin φ {ζ} (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact hφζ) _ (a : ↥KN).2
    rw [hφ] at this
    exact this
  ·
    exact haα.symm
  ·
    intro τ hτ hτμ k hk
    have hτk : τ ∈ k₀.fixingSubgroup := by rw [hfix]; exact hτ
    let φ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ :=
      IntermediateField.fixingSubgroupEquiv k₀ ⟨τ, hτk⟩
    have hφ : ∀ y, φ y = τ y := fun _ => rfl
    have hφKN : φ ∈ KN.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      have hφζ : φ ζ = ζ := by rw [hφ]; exact hτμ ζ hζ.pow_eq_one
      exact fixes_adjoin φ {ζ} (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact hφζ)
    have hρφ : ρ ⟨φ, hφKN⟩ = τ := AlgEquiv.ext fun _ => rfl
    have hval := congrArg (fun u : (AlgebraicClosure ℚ)ˣ => (u : AlgebraicClosure ℚ)) (hχ' ⟨φ, hφKN⟩)
    simp only at hval
    rw [hχ'_apply, hρφ, kummerCocycle_apply, Units.val_div_eq_div_val, val_smul_units] at hval

    have hγ0 : (α : AlgebraicClosure ℚ) ≠ 0 := α.ne_zero
    have hq : (φ : AlgebraicClosure ℚ ≃ₐ[↥k₀] AlgebraicClosure ℚ) (α : AlgebraicClosure ℚ) / α =
        (ζ ^ p ^ (N - n)) ^ k := by
      rw [hφ, hk, mul_div_assoc, div_self hγ0, mul_one]
    rw [hq] at hval

    have hζu_prim : IsPrimitiveRoot ζu (p ^ n) := by
      have h' : IsPrimitiveRoot (ζu : AlgebraicClosure ℚ) (p ^ n) := by rw [hζu]; exact hζn
      exact IsPrimitiveRoot.coe_units_iff.mp h'
    have hvalU : ζu ^ (χ τ).val = ζu ^ k := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hζu]; exact hval)
    rw [pow_eq_pow_iff_modEq, ← hζu_prim.eq_orderOf] at hvalU
    rw [← ZMod.natCast_zmod_val (χ τ)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hvalU

end S_ValuationSubring_exists_kummer_generator_of_additive_inertia_character
end P2MW
export P2MW.S_ValuationSubring_exists_kummer_generator_of_additive_inertia_character (solution)
