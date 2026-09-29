-- Prove2me | solution 1 for ValuationSubring.exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c018611d-4acb-591d-a276-aab86248be49

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Theorems.Thm_ValuationSubring_exists_eq_tameCharacter_pow_of_pow_eq_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
import Theorems.Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem
import Theorems.Thm_ValuationSubring_tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

private theorem ssX1_not_dvd (q : ℕ) [hq : Fact q.Prime] : ¬ q ∣ q ^ 2 - 1 := by
  intro h
  have h2 : q ∣ q ^ 2 := dvd_pow_self q two_ne_zero
  have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.out.pos
  have h3 : q ^ 2 = (q ^ 2 - 1) + 1 := (Nat.sub_add_cancel hpos).symm
  rw [h3] at h2
  exact hq.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h2))

private theorem ssX1_exp_ne_zero (q : ℕ) [hq : Fact q.Prime] : q ^ 2 - 1 ≠ 0 := by
  have h : 2 ≤ q := hq.out.two_le
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  omega

private theorem ssX1_cast_ne_zero (q : ℕ) [hq : Fact q.Prime] : (q : AlgebraicClosure ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr hq.out.ne_zero

private theorem ssX1_root_ne_zero (q : ℕ) [Fact q.Prime] {π : AlgebraicClosure ℚ}
    (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) : π ≠ 0 := by
  rintro rfl
  rw [zero_pow (ssX1_exp_ne_zero q)] at hπ
  exact ssX1_cast_ne_zero q hπ.symm

private theorem ssX1_isUnit_of_pow {K : Type} [CommMonoid K] {x : K} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    IsUnit x := by
  have hn' : n = (n - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero hn).symm
  refine ⟨⟨x, x ^ (n - 1), ?_, ?_⟩, rfl⟩
  · rw [← pow_succ', ← hn', hx]
  · rw [← pow_succ, ← hn', hx]

private theorem ssX1_mem_of_pow_eq_one (P : ValuationSubring (AlgebraicClosure ℚ)) {x : AlgebraicClosure ℚ}
    {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) : x ∈ P := by
  rcases P.mem_or_inv_mem x with h | h
  · exact h
  · have hx' : x = (x⁻¹) ^ (n - 1) := by
      have hn' : n = (n - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero hn).symm
      have h1 : x⁻¹ = x ^ (n - 1) := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', ← hn', hx])
      rw [inv_pow, ← h1, inv_inv]
    rw [hx']
    exact pow_mem h _

private theorem ssX1_a_one {O'' : Type} [CommRing O''] [IsDomain O'']
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a (σ * τ) = a σ * a τ) :
    a 1 = 1 := by
  have h := hmul 1 (one_mem _) 1 (one_mem _)
  rw [one_mul] at h
  have h' : a 1 * 1 = a 1 * a 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

private theorem ssX1_a_pow {O'' : Type} [CommRing O''] [IsDomain O'']
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a (σ * τ) = a σ * a τ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (n : ℕ) :
    a (σ ^ n) = a σ ^ n := by
  induction n with
  | zero => simpa using ssX1_a_one P a hmul
  | succ n ih => rw [pow_succ, hmul _ (pow_mem hσ n) _ hσ, ih, pow_succ]

private theorem ssX1_tc_pow (P : ValuationSubring (AlgebraicClosure ℚ)) {π : AlgebraicClosure ℚ} (hπ : π ≠ 0)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (n : ℕ) :
    P.tameCharacter π (σ ^ n) = P.tameCharacter π σ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    unfold ValuationSubring.tameCharacter
    have hmem : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π ∈ P := by
      simp [div_self hπ]
    rw [dif_pos hmem]
    have h1 : (⟨(1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π, hmem⟩ : P) = 1 := by
      ext; simp [div_self hπ]
    rw [h1, map_one]
  | succ n ih =>
    rw [pow_succ, P.tameCharacter_mul_of_mem_inertiaSubgroupIn π hπ (pow_mem hσ n) σ, ih, pow_succ]

private theorem ssX1_tc_eq (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    {π π₀ : AlgebraicClosure ℚ} (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (hπ₀ : π₀ ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π σ = P.tameCharacter π₀ σ := by
  intro σ hσ
  have h0 := ssX1_root_ne_zero q hπ
  have h0' := ssX1_root_ne_zero q hπ₀
  have hu : π / π₀ ∈ P :=
    ssX1_mem_of_pow_eq_one P (ssX1_exp_ne_zero q) (by rw [div_pow, hπ, hπ₀, div_self (ssX1_cast_ne_zero q)])
  have hu' : π₀ / π ∈ P :=
    ssX1_mem_of_pow_eq_one P (ssX1_exp_ne_zero q) (by rw [div_pow, hπ, hπ₀, div_self (ssX1_cast_ne_zero q)])
  exact P.tameCharacter_eq_of_div_mem_of_div_mem π₀ π h0' h0 hu hu' hσ

private theorem ssX1_exists_sigma (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {π₀ : AlgebraicClosure ℚ} (hπ₀ : π₀ ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (x : IsLocalRing.ResidueField P) (hx : x ^ (q ^ 2 - 1) = 1) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π₀ σ = x := by
  haveI : NeZero (q ^ 2 - 1) := ⟨ssX1_exp_ne_zero q⟩
  obtain ⟨σ₁, hσ₁, hprim⟩ :=
    P.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter (Fact.out : q.Prime) hP (ssX1_not_dvd q) hπ₀
  have hxu : IsUnit x := ssX1_isUnit_of_pow (ssX1_exp_ne_zero q) hx
  obtain ⟨ξ, hξ⟩ := hprim.isUnit (ssX1_exp_ne_zero q)
  have hξprim : IsPrimitiveRoot ξ (q ^ 2 - 1) := IsPrimitiveRoot.coe_units_iff.mp (by rw [hξ]; exact hprim)
  have hmem : hxu.unit ∈ rootsOfUnity (q ^ 2 - 1) (IsLocalRing.ResidueField P) := by
    rw [mem_rootsOfUnity]; ext; simp [hx]
  obtain ⟨i, -, hi⟩ := hξprim.eq_pow_of_mem_rootsOfUnity hmem
  refine ⟨σ₁ ^ i, pow_mem hσ₁ i, ?_⟩
  rw [ssX1_tc_pow P (ssX1_root_ne_zero q hπ₀) hσ₁ i, ← hξ]
  have := congrArg Units.val hi
  rw [Units.val_pow_eq_pow_val] at this
  rw [this]; simp

private theorem ssX1_pow_of_primitive (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {π₀ : AlgebraicClosure ℚ} (hπ₀ : π₀ ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hprim : IsPrimitiveRoot (P.tameCharacter π₀ σ₀) (q ^ 2 - 1)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ n : ℕ, P.tameCharacter π₀ σ = P.tameCharacter π₀ σ₀ ^ n := by
  intro σ hσ
  haveI : NeZero (q ^ 2 - 1) := ⟨ssX1_exp_ne_zero q⟩
  have hx : P.tameCharacter π₀ σ ^ (q ^ 2 - 1) = 1 :=
    P.tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn q hP π₀ hπ₀ σ hσ
  have hxu : IsUnit (P.tameCharacter π₀ σ) := ssX1_isUnit_of_pow (ssX1_exp_ne_zero q) hx
  obtain ⟨ξ, hξ⟩ := hprim.isUnit (ssX1_exp_ne_zero q)
  have hξprim : IsPrimitiveRoot ξ (q ^ 2 - 1) := IsPrimitiveRoot.coe_units_iff.mp (by rw [hξ]; exact hprim)
  have hmem : hxu.unit ∈ rootsOfUnity (q ^ 2 - 1) (IsLocalRing.ResidueField P) := by
    rw [mem_rootsOfUnity]; ext; simp [hx]
  obtain ⟨i, -, hi⟩ := hξprim.eq_pow_of_mem_rootsOfUnity hmem
  refine ⟨i, ?_⟩
  have := congrArg Units.val hi
  rw [Units.val_pow_eq_pow_val, hξ] at this
  rw [this]; simp

private theorem ssX1_hom_of_generator {G H : Type} [Group G] [CommGroup H] (g : G)
    (hg : ∀ x : G, x ∈ Submonoid.powers g) (u : H) (hu : orderOf u ∣ orderOf g) :
    ∃ θ : G →* H, θ g = u ∧ (orderOf u = orderOf g → Function.Injective θ) := by
  classical

  have hex : ∀ x : G, ∃ n : ℕ, g ^ n = x := fun x => (Submonoid.mem_powers_iff x g).mp (hg x)
  choose e he using hex

  have hpow : ∀ i j : ℕ, g ^ i = g ^ j → u ^ i = u ^ j := by
    intro i j hij
    rw [pow_eq_pow_iff_modEq] at hij ⊢
    exact hij.of_dvd hu
  refine ⟨MonoidHom.mk' (fun x => u ^ e x) ?_, ?_, ?_⟩
  · intro x y
    rw [← pow_add]
    apply hpow
    rw [pow_add, he, he, he]
  · show u ^ e g = u
    have h1 : u ^ e g = u ^ 1 := hpow _ _ (by rw [he, pow_one])
    rw [h1, pow_one]
  · intro hord x y hxy
    change u ^ e x = u ^ e y at hxy
    rw [← he x, ← he y]
    rw [pow_eq_pow_iff_modEq] at hxy ⊢
    rw [← hord]
    exact hxy

private theorem ssX1_engine (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {O'' : Type} [CommRing O''] [IsDomain O'']
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a (σ * τ) = a σ * a τ)
    (hpow : ∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1)
    {π₀ : AlgebraicClosure ℚ} (hπ₀ : π₀ ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      P.tameCharacter π₀ σ = P.tameCharacter π₀ τ → a σ = a τ := by
  classical
  intro σ hσ τ hτ hστ
  haveI : NeZero (q ^ 2 - 1) := ⟨ssX1_exp_ne_zero q⟩
  haveI := rootsOfUnity.isCyclic O'' (q ^ 2 - 1)

  have hmemR : ∀ ρ ∈ P.inertiaSubgroupIn ℚ, a ρ ∈ rootsOfUnity (q ^ 2 - 1) O'' := fun ρ hρ =>
    (mem_rootsOfUnity _ _).mpr (hpow ρ hρ)

  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity (q ^ 2 - 1) O'')
  have hζpow : ζ ^ (q ^ 2 - 1) = 1 := by
    refine Subtype.ext ?_
    simpa using (mem_rootsOfUnity _ _).mp ζ.2
  have hd : orderOf ζ ∣ q ^ 2 - 1 := orderOf_dvd_of_pow_eq_one hζpow

  obtain ⟨σ₁, -, hprim⟩ :=
    P.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter (Fact.out : q.Prime) hP (ssX1_not_dvd q) hπ₀
  obtain ⟨ξ, hξ⟩ := hprim.isUnit (ssX1_exp_ne_zero q)
  have hξprim : IsPrimitiveRoot ξ (q ^ 2 - 1) := IsPrimitiveRoot.coe_units_iff.mp (by rw [hξ]; exact hprim)
  have hηprim : IsPrimitiveRoot (ξ ^ ((q ^ 2 - 1) / orderOf ζ)) (orderOf ζ) :=
    hξprim.pow (Nat.pos_of_ne_zero (ssX1_exp_ne_zero q)) (Nat.div_mul_cancel hd).symm
  have hηord : orderOf (ξ ^ ((q ^ 2 - 1) / orderOf ζ)) = orderOf ζ := hηprim.eq_orderOf.symm

  obtain ⟨χ, -, hχinj⟩ := ssX1_hom_of_generator ζ hζ (ξ ^ ((q ^ 2 - 1) / orderOf ζ)) (dvd_of_eq hηord)
  have hχ : Function.Injective χ := hχinj hηord

  let ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P := fun ρ =>
    if h : ρ ∈ P.inertiaSubgroupIn ℚ then ((χ ⟨a ρ, hmemR ρ h⟩ : (IsLocalRing.ResidueField P)ˣ) :
      IsLocalRing.ResidueField P) else 1
  have hψ : ∀ ρ (h : ρ ∈ P.inertiaSubgroupIn ℚ), ψ ρ = ((χ ⟨a ρ, hmemR ρ h⟩ : (IsLocalRing.ResidueField P)ˣ) :
      IsLocalRing.ResidueField P) := fun ρ h => dif_pos h
  have hψmul : ∀ ρ₁ ∈ P.inertiaSubgroupIn ℚ, ∀ ρ₂ ∈ P.inertiaSubgroupIn ℚ, ψ (ρ₁ * ρ₂) = ψ ρ₁ * ψ ρ₂ := by
    intro ρ₁ h₁ ρ₂ h₂
    rw [hψ _ (mul_mem h₁ h₂), hψ _ h₁, hψ _ h₂, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp [hmul ρ₁ h₁ ρ₂ h₂]
  have hψord : ∀ ρ ∈ P.inertiaSubgroupIn ℚ, ψ ρ ^ (q ^ 2 - 1) = 1 := by
    intro ρ h
    rw [hψ _ h, ← Units.val_pow_eq_pow_val, ← map_pow]
    have h1 : (⟨a ρ, hmemR ρ h⟩ : rootsOfUnity (q ^ 2 - 1) O'') ^ (q ^ 2 - 1) = 1 := by
      ext
      simp [hpow ρ h]
    rw [h1, map_one, Units.val_one]

  obtain ⟨j, -, hj⟩ :=
    P.exists_eq_tameCharacter_pow_of_pow_eq_one (Fact.out : q.Prime) hP (ssX1_not_dvd q) hπ₀ ψ hψmul hψord
  have hψeq : ψ σ = ψ τ := by rw [hj σ hσ, hj τ hτ, hστ]
  rw [hψ _ hσ, hψ _ hτ] at hψeq
  have h2 := hχ (Units.ext hψeq)
  exact congrArg Subtype.val h2

private theorem ssX1_ringHom_eq_or (q : ℕ) [Fact q.Prime] {K : Type} [Field K]
    (ι ι₀ : GaloisField q 2 →+* K) :
    (∀ x : GaloisField q 2, ι x = ι₀ x) ∨ (∀ x : GaloisField q 2, ι x = ι₀ (x ^ q)) := by
  classical

  set F := GaloisField q 2 with hF
  letI : Fintype F := Fintype.ofFinite F

  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  set p : Polynomial K := Polynomial.X ^ Fintype.card F - Polynomial.X with hp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hcard
  have hroot : ∀ (φ : F →+* K) (x : F), φ x ∈ p.roots := by
    intro φ x
    rw [Polynomial.mem_roots hp0, hp, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, ← map_pow, FiniteField.pow_card, sub_self]
  set S : Finset K := Finset.univ.image ι₀ with hS
  have hScard : S.card = Fintype.card F := by
    rw [hS, Finset.card_image_of_injective _ ι₀.injective, Finset.card_univ]
  have hSsub : S ⊆ p.roots.toFinset := by
    intro y hy
    rw [hS, Finset.mem_image] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact Multiset.mem_toFinset.mpr (hroot ι₀ x)
  have hroots_card : p.roots.toFinset.card ≤ Fintype.card F := by
    calc p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = Fintype.card F := FiniteField.X_pow_card_sub_X_natDegree_eq K hcard
  have hSeq : S = p.roots.toFinset := Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hroots_card)
  have hmemS : ∀ x : F, ∃ y : F, ι₀ y = ι x := by
    intro x
    have h : ι x ∈ S := by rw [hSeq]; exact Multiset.mem_toFinset.mpr (hroot ι x)
    rw [hS, Finset.mem_image] at h
    obtain ⟨y, -, hy⟩ := h
    exact ⟨y, hy⟩
  choose e he using hmemS

  have hinj := ι₀.injective
  let e' : F →+* F :=
    { toFun := e
      map_one' := hinj (by rw [he, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [he, map_mul, map_mul, he, he])
      map_zero' := hinj (by rw [he, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [he, map_add, map_add, he, he]) }

  let e'' : F →ₐ[ZMod q] F :=
    { e' with
      commutes' := fun r => by
        have h : e'.comp (algebraMap (ZMod q) F) = algebraMap (ZMod q) F := Subsingleton.elim _ _
        exact congrArg (fun f : ZMod q →+* F => f r) h }

  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod q) F).2 e''
  have hn2 : (n : ℕ) < 2 := by
    have h1 : (n : ℕ) < Module.finrank (ZMod q) F := n.isLt
    have h2 : Module.finrank (ZMod q) F = 2 := GaloisField.finrank q two_ne_zero
    omega
  have hfrob : ∀ x : F, FiniteField.frobeniusAlgHom (ZMod q) F x = x ^ q := by
    intro x
    rw [FiniteField.coe_frobeniusAlgHom, ZMod.card]
  have hn' : FiniteField.frobeniusAlgHom (ZMod q) F ^ (n : ℕ) = e'' := hn
  have he_eq : ∀ x : F, e x = (FiniteField.frobeniusAlgHom (ZMod q) F ^ (n : ℕ)) x := by
    intro x
    rw [hn']
    rfl
  have hι : ∀ x : F, ι x = ι₀ (e x) := fun x => (he x).symm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k := ⟨_, rfl⟩
  rw [hk] at he_eq hn2
  interval_cases k
  · left
    intro x
    rw [hι x, he_eq x, pow_zero, AlgHom.one_apply]
  · right
    intro x
    rw [hι x, he_eq x, pow_one, hfrob]

private theorem ssX1_card_units (q : ℕ) [Fact q.Prime] : Nat.card (GaloisField q 2)ˣ = q ^ 2 - 1 := by
  rw [Nat.card_units, GaloisField.card q 2 two_ne_zero]

private theorem ssX1_orderOf_generator (q : ℕ) [Fact q.Prime] (g : (GaloisField q 2)ˣ)
    (hg : ∀ x : (GaloisField q 2)ˣ, x ∈ Submonoid.powers g) : orderOf g = q ^ 2 - 1 := by
  rw [← ssX1_card_units q]
  apply orderOf_eq_card_of_forall_mem_zpowers
  intro x
  obtain ⟨n, rfl⟩ := hg x
  exact Subgroup.npow_mem_zpowers g n

private theorem ssX1_riders (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    {O'' : Type} [CommRing O''] [IsDomain O'']
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ) (θ : (GaloisField q 2)ˣ →* O''ˣ)
    (h₁ : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ α : (GaloisField q 2)ˣ, a σ = θ α)
    (h₂ : ∀ α : (GaloisField q 2)ˣ, ∃ σ ∈ P.inertiaSubgroupIn ℚ, θ α = a σ) :
    ((∃ τ ∈ P.inertiaSubgroupIn ℚ, a τ ^ (q - 1) ≠ 1) ↔ θ ^ q ≠ θ) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q + 1) = 1) ↔ θ ^ (q + 1) = 1) := by
  have hq1 : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_ne_zero (Fact.out : q.Prime).ne_zero).symm

  have hkey : ∀ x : O''ˣ, x ^ q = x ↔ x ^ (q - 1) = 1 := by
    intro x
    conv_lhs => rw [hq1, pow_succ]
    constructor
    · intro h
      have h' : x ^ (q - 1) * x = 1 * x := by rw [h, one_mul]
      exact mul_right_cancel h'
    · intro h
      rw [h, one_mul]
  constructor
  · constructor
    · rintro ⟨τ, hτ, hne⟩ heq
      obtain ⟨α, hα⟩ := h₁ τ hτ
      apply hne
      rw [hα, ← hkey]
      have := congrArg (fun f : (GaloisField q 2)ˣ →* O''ˣ => f α) heq
      simpa using this
    · intro hne
      by_contra hall
      push Not at hall
      apply hne
      refine MonoidHom.ext fun α => ?_
      obtain ⟨σ, hσ, hσα⟩ := h₂ α
      have h1 : θ α ^ (q - 1) = 1 := by rw [hσα]; exact hall σ hσ
      simpa using (hkey (θ α)).mpr h1
  · constructor
    · intro hall
      refine MonoidHom.ext fun α => ?_
      obtain ⟨σ, hσ, hσα⟩ := h₂ α
      simpa [hσα] using hall σ hσ
    · intro heq σ hσ
      obtain ⟨α, hα⟩ := h₁ σ hσ
      have := congrArg (fun f : (GaloisField q 2)ˣ →* O''ˣ => f α) heq
      simp at this
      rw [hα]; exact this

private theorem ssX1_core (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {O'' : Type} [CommRing O''] [IsDomain O'']
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a (σ * τ) = a σ * a τ)
    (hpow : ∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1)
    {π₀ : AlgebraicClosure ℚ} (hπ₀ : π₀ ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (g : (GaloisField q 2)ˣ) (hg : ∀ x : (GaloisField q 2)ˣ, x ∈ Submonoid.powers g)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ₀ : σ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hgen : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ n : ℕ, P.tameCharacter π₀ σ = P.tameCharacter π₀ σ₀ ^ n)
    (θ : (GaloisField q 2)ˣ →* O''ˣ) (hθ : θ g = a σ₀) :
    (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ α : (GaloisField q 2)ˣ, a σ = θ α) ∧
      (∀ α : (GaloisField q 2)ˣ, ∃ σ ∈ P.inertiaSubgroupIn ℚ, θ α = a σ) ∧
      (∀ ι₀ : GaloisField q 2 →+* IsLocalRing.ResidueField P, ι₀ (g : GaloisField q 2) = P.tameCharacter π₀ σ₀ →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
          ι₀ (α : GaloisField q 2) = P.tameCharacter π₀ σ → a σ = θ α) := by
  have hπ0 := ssX1_root_ne_zero q hπ₀
  have heng := ssX1_engine q P hP a hmul hpow hπ₀

  have hstep : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ n : ℕ,
      P.tameCharacter π₀ σ = P.tameCharacter π₀ σ₀ ^ n → a σ = θ (g ^ n) := by
    intro σ hσ n hn
    have h1 : a σ = a (σ₀ ^ n) :=
      heng σ hσ (σ₀ ^ n) (pow_mem hσ₀ n) (by rw [hn, ssX1_tc_pow P hπ0 hσ₀ n])
    rw [h1, ssX1_a_pow P a hmul hσ₀ n, map_pow, hθ]
  refine ⟨?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨n, hn⟩ := hgen σ hσ
    exact ⟨g ^ n, hstep σ hσ n hn⟩
  · intro α
    obtain ⟨n, rfl⟩ := hg α
    refine ⟨σ₀ ^ n, pow_mem hσ₀ n, ?_⟩
    rw [map_pow, hθ, ssX1_a_pow P a hmul hσ₀ n]
  · intro ι₀ hι₀ σ hσ α hα
    obtain ⟨n, rfl⟩ := hg α
    apply hstep σ hσ n
    rw [← hα, Units.val_pow_eq_pow_val, map_pow, hι₀]

theorem solution
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {O'' : Type} [CommRing O''] [IsDomain O'']
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a (σ * τ) = a σ * a τ)
    (hpow : ∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1) :
    ∃ θ : (GaloisField q 2)ˣ →* O''ˣ,
      (∀ (π : AlgebraicClosure ℚ), π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) →
        ∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P,
          (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π σ → a σ = θ α) ∨
          (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π σ → a σ = θ (α ^ q))) ∧
      ((∃ τ ∈ P.inertiaSubgroupIn ℚ, a τ ^ (q - 1) ≠ 1) ↔ θ ^ q ≠ θ) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q + 1) = 1) ↔ θ ^ (q + 1) = 1) := by
  classical
  haveI : NeZero (q ^ 2 - 1) := ⟨ssX1_exp_ne_zero q⟩
  obtain ⟨π₀, hπ₀⟩ :=
    IsAlgClosed.exists_pow_nat_eq (q : AlgebraicClosure ℚ) (Nat.pos_of_ne_zero (ssX1_exp_ne_zero q))
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (GaloisField q 2)ˣ)
  have hordg : orderOf g = q ^ 2 - 1 := ssX1_orderOf_generator q g hg

  have key : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, IsPrimitiveRoot (P.tameCharacter π₀ σ₀) (q ^ 2 - 1) ∧
      ∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P, ∃ ι₁ : GaloisField q 2 →+* IsLocalRing.ResidueField P,
        ι₁ (g : GaloisField q 2) = P.tameCharacter π₀ σ₀ := by
    by_cases hemb : Nonempty (GaloisField q 2 →+* IsLocalRing.ResidueField P)
    · obtain ⟨ι₀⟩ := hemb
      have hgprim : IsPrimitiveRoot (g : GaloisField q 2) (q ^ 2 - 1) := by
        have h := IsPrimitiveRoot.orderOf g
        rw [hordg] at h
        exact IsPrimitiveRoot.coe_units_iff.mpr h
      have hx : ι₀ (g : GaloisField q 2) ^ (q ^ 2 - 1) = 1 := by rw [← map_pow, hgprim.pow_eq_one, map_one]
      obtain ⟨σ₀, hσ₀, hσ₀x⟩ := ssX1_exists_sigma q P hP hπ₀ _ hx
      refine ⟨σ₀, hσ₀, ?_, fun _ => ⟨ι₀, hσ₀x.symm⟩⟩
      rw [hσ₀x]
      exact (IsPrimitiveRoot.map_iff_of_injective ι₀.injective).mpr hgprim
    · obtain ⟨σ₀, hσ₀, hprim⟩ :=
        P.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter (Fact.out : q.Prime) hP (ssX1_not_dvd q) hπ₀
      exact ⟨σ₀, hσ₀, hprim, fun ι => (hemb ⟨ι⟩).elim⟩
  obtain ⟨σ₀, hσ₀, hprim, hemb⟩ := key
  have hgen := ssX1_pow_of_primitive q P hP hπ₀ hprim
  have hu : orderOf (a σ₀) ∣ orderOf g := by rw [hordg]; exact orderOf_dvd_of_pow_eq_one (hpow σ₀ hσ₀)
  obtain ⟨θ, hθ, -⟩ := ssX1_hom_of_generator g hg (a σ₀) hu
  obtain ⟨h₁, h₂, hexact⟩ := ssX1_core q P hP a hmul hpow hπ₀ g hg hσ₀ hgen θ hθ
  refine ⟨θ, ?_, ssX1_riders q P a θ h₁ h₂⟩
  intro π hπ ι
  obtain ⟨ι₁, hι₁⟩ := hemb ι
  have hex := hexact ι₁ hι₁
  have htc := ssX1_tc_eq q P hπ hπ₀
  rcases ssX1_ringHom_eq_or q ι ι₁ with h | h
  · left
    intro σ hσ α hα
    exact hex σ hσ α (by rw [← h, hα, htc σ hσ])
  · right
    intro σ hσ α hα
    have hα' : ι₁ ((α ^ q : (GaloisField q 2)ˣ) : GaloisField q 2) = P.tameCharacter π₀ σ := by
      rw [Units.val_pow_eq_pow_val, ← h, hα, htc σ hσ]
    exact hex σ hσ (α ^ q) hα'

end S_ValuationSubring_exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow
end P2MW
export P2MW.S_ValuationSubring_exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow (solution)
