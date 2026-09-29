-- Prove2me | solution 1 for ResidualGaloisRep.exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/30aff226-9abf-5f32-8f2d-fa05d945ae18

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
import Theorems.Thm_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker
import Theorems.Thm_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation IntermediateField Module

noncomputable section

namespace P2mCheb

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ
  rfl
  rfl
scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

section Cocycles

variable {R G : Type} [CommRing R] [Group G] {A : Rep R G}

def Splits (x : cocycles₁ A) (g : G) : Prop := x g ∈ LinearMap.range (A.ρ g - 1)

lemma splits_iff (x : cocycles₁ A) (g : G) : Splits x g ↔ ∃ a : A, x g = A.ρ g a - a := by
  simp only [Splits, LinearMap.mem_range, LinearMap.sub_apply, Module.End.one_apply, eq_comm]

lemma apply_pow_of_apply_eq (x : cocycles₁ A) {g : G} {a : A} (h : x g = A.ρ g a - a)
    (j : ℕ) : x (g ^ j) = A.ρ (g ^ j) a - a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, (mem_cocycles₁_iff x).1 x.2, h, ih, map_mul, Module.End.mul_apply, map_sub]
    abel

lemma splits_pow {x : cocycles₁ A} {g : G} (h : Splits x g) (j : ℕ) : Splits x (g ^ j) := by
  obtain ⟨a, ha⟩ := (splits_iff x g).1 h
  exact (splits_iff x _).2 ⟨a, apply_pow_of_apply_eq x ha j⟩

lemma splits_of_isConj {x : cocycles₁ A} {g g' : G} (hc : IsConj g g') (h : Splits x g) :
    Splits x g' := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  obtain ⟨a, ha⟩ := (splits_iff x g).1 h
  have hcg : g' * c = c * g := by rw [← hc]; group
  have h1 := (mem_cocycles₁_iff x).1 x.2 g' c
  have h2 := (mem_cocycles₁_iff x).1 x.2 c g
  rw [hcg, h2, ha, map_sub] at h1
  have h3 : A.ρ g' (A.ρ c a) = A.ρ c (A.ρ g a) := by
    rw [← Module.End.mul_apply, ← map_mul, hcg, map_mul, Module.End.mul_apply]
  refine (splits_iff x g').2 ⟨A.ρ c a - x c, ?_⟩
  rw [map_sub, h3]
  have h4 : x g' = A.ρ c (A.ρ g a) - A.ρ c a + x c - A.ρ g' (x c) := by rw [h1]; abel
  rw [h4]; abel

lemma splits_mul_iff {x : cocycles₁ A} {g h : G} (hρ : A.ρ h = 1) (hx : x h = 0) :
    Splits x (g * h) ↔ Splits x g := by
  have hgh : x (g * h) = x g := by
    rw [(mem_cocycles₁_iff x).1 x.2, hx, map_zero, zero_add]
  simp only [Splits, hgh, map_mul, hρ, mul_one]

lemma map_H1π_ne_zero_of_not_splits {C : Type} [Group C] (f : C →* G) (c₀ : C)
    {x : cocycles₁ A} (h : ¬ Splits x (f c₀)) :
    (map f (𝟙 (Rep.res f A)) 1).hom (H1π A x) ≠ 0 := by
  intro h0
  apply h
  have h0' : H1π (Rep.res f A) (mapCocycles₁ f (𝟙 (Rep.res f A)) x) = 0 := by
    rw [← H1π_comp_map_apply]; exact h0
  obtain ⟨a, ha⟩ := (H1π_eq_zero_iff _).1 h0'
  refine (splits_iff x _).2 ⟨a, ?_⟩
  have := congr_fun ha c₀
  simp [coe_mapCocycles₁ (x := x)] at this
  exact this.symm

end Cocycles

section LinAlg

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

lemma charpoly_eq_of_finrank_eq_two (hV : finrank k V = 2) (T : Module.End k V) :
    T.charpoly = X ^ 2 - C (LinearMap.trace k V T) * X + C (LinearMap.det T) := by
  let b := Module.finBasisOfFinrankEq k V hV
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace k b T, LinearMap.det_toMatrix b T]

lemma charpoly_eq_mul_iff (hV : finrank k V = 2) (T : Module.End k V) (a b : k) :
    T.charpoly = (X - C a) * (X - C b) ↔
      LinearMap.trace k V T = a + b ∧ LinearMap.det T = a * b := by
  have hexp : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
    simp only [map_add, map_mul]; ring
  rw [charpoly_eq_of_finrank_eq_two hV, hexp]
  constructor
  · intro h
    have h1 := congrArg (fun q : k[X] => q.coeff 1) h
    have h0 := congrArg (fun q : k[X] => q.coeff 0) h
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at h1 h0
    norm_num at h1 h0
    exact ⟨by linear_combination -h1, h0⟩
  · rintro ⟨h1, h0⟩
    rw [h1, h0]

lemma charpoly_conj_eq (hV : finrank k V = 2) {T P Q : Module.End k V} (hPQ : Q * P = 1)
    {a b : k} (h : T.charpoly = (X - C a) * (X - C b)) :
    (P * T * Q).charpoly = (X - C a) * (X - C b) := by
  rw [charpoly_eq_mul_iff hV] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [LinearMap.trace_mul_comm, ← mul_assoc, hPQ, one_mul, h.1]
  · rw [map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, hPQ, map_one, one_mul, h.2]

lemma exists_basis_toMatrix_eq_diagonal (hV : finrank k V = 2) {T : Module.End k V} {α β : k}
    (hαβ : α ≠ β) (h : T.charpoly = (X - C α) * (X - C β)) :
    ∃ b : Basis (Fin 2) k V, LinearMap.toMatrix b b T = Matrix.diagonal ![α, β] := by
  have hα : T.HasEigenvalue α :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [h]; simp)
  have hβ : T.HasEigenvalue β :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [h]; simp)
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  obtain ⟨w, hw⟩ := hβ.exists_hasEigenvector
  have hv1 : T v = α • v := hv.apply_eq_smul
  have hw1 : T w = β • w := hw.apply_eq_smul
  have hli : LinearIndependent k ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : (s * α) • v + (t * β) • w = 0 := by
      have := congrArg T hst
      rw [map_add, map_smul, map_smul, hv1, hw1, smul_smul, smul_smul, map_zero] at this
      exact this
    have h3 : (s * β) • v + (t * β) • w = 0 := by
      have := congrArg (fun u => β • u) hst
      simp only [smul_add, smul_smul, smul_zero] at this
      rw [mul_comm β s, mul_comm β t] at this
      exact this
    have h4 : (s * (α - β)) • v = 0 := by
      have := sub_eq_zero.2 (h2.trans h3.symm)
      rw [add_sub_add_right_eq_sub, ← sub_smul, ← mul_sub] at this
      exact this
    have hs : s = 0 := by
      rcases smul_eq_zero.1 h4 with h | h
      · exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hαβ)
      · exact absurd h hv.2
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.1 hst).resolve_right hw.2⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV]), ?_⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV] : Fintype.card (Fin 2) = _)
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = w := by simp [b]
  have hT0 : T (b 0) = α • b 0 := by rw [hb0, hv1]
  have hT1 : T (b 1) = β • b 1 := by rw [hb1, hw1]
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hT0, hT1, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]

lemma charpoly_pow_and (hV : finrank k V = 2) {T : Module.End k V} {α β : k}
    (hαβ : α ≠ β) (h : T.charpoly = (X - C α) * (X - C β)) (m : ℕ) :
    (T ^ m).charpoly = (X - C (α ^ m)) * (X - C (β ^ m)) ∧
      (α ^ m = β ^ m → T ^ m = (α ^ m) • 1) ∧
      (∀ γ : k, T = γ • 1 → False) := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_toMatrix_eq_diagonal hV hαβ h
  have hpow : ∀ m : ℕ, LinearMap.toMatrix b b (T ^ m) = Matrix.diagonal ![α ^ m, β ^ m] := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, LinearMap.toMatrix_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    | succ m ih =>
      rw [pow_succ, LinearMap.toMatrix_mul, ih, hb, Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ]
  refine ⟨?_, ?_, ?_⟩
  · rw [← LinearMap.charpoly_toMatrix (T ^ m) b, hpow m, Matrix.charpoly_fin_two,
      Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, sub_zero, map_add, map_mul]
    ring
  · intro hγ
    apply (LinearMap.toMatrix b b).injective
    rw [hpow m, LinearEquiv.map_smul, LinearMap.toMatrix_one, hγ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro γ hγ
    apply hαβ
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) hb
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 1) hb
    rw [hγ, LinearEquiv.map_smul, LinearMap.toMatrix_one] at h0 h1
    simp at h0 h1
    rw [← h0, ← h1]

end LinAlg

theorem main
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {p : ℕ} [Fact p.Prime] {n : ℕ} {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {R : Type} [CommRing R] (M : Rep R (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hM : ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ s ∈ E.fixingSubgroup, M.ρ s = 1)
    (c : cocycles₁ M)
    (hc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s, s ∈ F.fixingSubgroup → c (g * s) = c g)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσζ : σ ζ = ζ)
    {α β : k} (hαβ : α ≠ β) (hσ : LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hcσ : c σ ∉ LinearMap.range (M.ρ σ - 1))
    (T : Finset ℕ) :
    ∃ q : Nat.Primes, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom (H1π M c) ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨E, hEfd, hE⟩ := hM
  obtain ⟨F, hFfd, hF⟩ := hc
  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hEfd; haveI := hFfd; haveI := hLfd
  have hζint : IsIntegral ℚ ζ := (isIntegral_algebraicClosure_rat).isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional hζint
  set E₁ : IntermediateField ℚ Qb := E ⊔ F ⊔ L ⊔ ℚ⟮ζ⟯ with hE₁
  haveI : FiniteDimensional ℚ E₁ := by
    rw [hE₁]
    haveI : FiniteDimensional ℚ (E ⊔ F : IntermediateField ℚ Qb) := finiteDimensional_sup E F
    haveI : FiniteDimensional ℚ (E ⊔ F ⊔ L : IntermediateField ℚ Qb) :=
      finiteDimensional_sup _ L
    exact finiteDimensional_sup _ _
  set E' : IntermediateField ℚ Qb := normalClosure ℚ E₁ Qb with hE'
  haveI hN : Normal ℚ E' := normalClosure.normal ℚ E₁ Qb
  haveI : FiniteDimensional ℚ E' := normalClosure.is_finiteDimensional ℚ E₁ Qb
  have hE₁E' : E₁ ≤ E' := le_normalClosure E₁
  have hEE' : E ≤ E' := le_trans (le_sup_left.trans (le_sup_left.trans le_sup_left)) hE₁E'
  have hFE' : F ≤ E' := le_trans (le_sup_right.trans (le_sup_left.trans le_sup_left)) hE₁E'
  have hLE' : L ≤ E' := le_trans (le_sup_right.trans le_sup_left) hE₁E'
  have hζE' : ζ ∈ E' := hE₁E' (le_sup_right (a := E ⊔ F ⊔ L) (mem_adjoin_simple_self ℚ ζ))
  set H : Subgroup Γ := E'.fixingSubgroup with hHdef
  have memH : ∀ h : Γ, h ∈ H ↔ ∀ x ∈ E', h x = x := fun h => by
    rw [hHdef]; exact IntermediateField.mem_fixingSubgroup_iff (K := E') h
  have hHM : ∀ h ∈ H, M.ρ h = 1 := fun h hh =>
    hE h ((IntermediateField.mem_fixingSubgroup_iff (K := E) h).2 fun x hx => (memH h).1 hh x (hEE' hx))
  have hHc : ∀ h ∈ H, ∀ g : Γ, c (g * h) = c g := fun h hh g =>
    hF g h ((IntermediateField.mem_fixingSubgroup_iff (K := F) h).2 fun x hx => (memH h).1 hh x (hFE' hx))
  have hHc0 : ∀ h ∈ H, c h = 0 := fun h hh => by
    have := hHc h hh 1
    rwa [one_mul, cocycles₁_map_one] at this
  have hHρ : ∀ h ∈ H, ρbar.ρ h = 1 := fun h hh => hL h fun x hx => (memH h).1 hh x (hLE' hx)
  have hHζ : ∀ h ∈ H, h ζ = ζ := fun h hh => (memH h).1 hh ζ hζE'

  let ρE : Γ →* (E' ≃ₐ[ℚ] E') := AlgEquiv.restrictNormalHom E'
  have key : ∀ (g : Γ) (x : E'), ((ρE g x : E') : Qb) = g x :=
    fun g x => AlgEquiv.restrictNormalHom_apply E' g x
  have hρE : ∀ g : Γ, ρE g = 1 ↔ g ∈ H := by
    intro g
    rw [memH]
    constructor
    · intro h x hx
      rw [← key g ⟨x, hx⟩, h]
      rfl
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      rw [key g x, AlgEquiv.one_apply]
      exact h x x.2
  have hkerH : ρE.ker = H := by
    ext g; rw [MonoidHom.mem_ker]; exact hρE g
  have modH : ∀ x y : Γ, ρE x = ρE y → ∃ h ∈ H, x = y * h := by
    intro x y hxy
    refine ⟨y⁻¹ * x, (hρE _).1 ?_, by group⟩
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hHopen : IsOpen (H : Set Γ) := IntermediateField.fixingSubgroup_isOpen E'
  have hkerOpen : IsOpen ((ρE.ker : Subgroup Γ) : Set Γ) := by rw [hkerH]; exact hHopen

  obtain ⟨B, hB⟩ := GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker ρE hkerOpen

  set N₀ : ℕ := p * ∏ t ∈ (T ∪ B).filter (· ≠ 0), t with hN₀
  have hN₀pos : 0 < N₀ := by
    refine Nat.mul_pos hp.pos (Finset.prod_pos fun t ht => ?_)
    exact Nat.pos_of_ne_zero (Finset.mem_filter.1 ht).2
  obtain ⟨ℓ, A, τ, g, e, m, hℓ, hℓN, hA, hτ, hmem1, hmem2⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen H hHopen σ hN₀pos
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact hℓN (Dvd.intro _ rfl)
  have hℓTB : ∀ t ∈ T ∪ B, ℓ ≠ t := by
    rintro t ht rfl
    apply hℓN
    rw [hN₀]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨ht, hℓ.ne_zero⟩)) _
  have hℓT : ℓ ∉ T := fun h => hℓTB ℓ (Finset.mem_union_left _ h) rfl
  have hℓB : ℓ ∉ B := fun h => hℓTB ℓ (Finset.mem_union_right _ h) rfl
  have hunrE : GlobalGaloisRep.IsUnramifiedAt ρE ℓ := hB ℓ hℓ hℓB
  set q : Nat.Primes := ⟨ℓ, hℓ⟩ with hq

  obtain ⟨τ', hτ'⟩ : ∃ τ' : Γ, τ' = g * τ * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : Γ, h₁ = g * τ ^ e * g⁻¹ * σ⁻¹ := ⟨_, rfl⟩
  obtain ⟨h₂, hh₂⟩ : ∃ h₂ : Γ, h₂ = g * τ * g⁻¹ * (σ ^ m)⁻¹ := ⟨_, rfl⟩
  have hm1 : h₁ ∈ H := hh₁ ▸ hmem1
  have hm2 : h₂ ∈ H := hh₂ ▸ hmem2
  have hτ'e : τ' ^ e = h₁ * σ := by rw [hτ', conj_pow, hh₁, inv_mul_cancel_right]
  have hτ'm : τ' = h₂ * σ ^ m := by rw [hh₂, hτ', inv_mul_cancel_right]

  have hσmζ : ∀ j : ℕ, (σ ^ j) ζ = ζ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hσζ, ih]
  have hτ'ζ : τ' ζ = ζ := by rw [hτ'm, AlgEquiv.mul_apply, hσmζ, hHζ h₂ hm2]
  have hτζ' : τ (g⁻¹ ζ) = g⁻¹ ζ := by
    have : τ = g⁻¹ * τ' * g := by rw [hτ']; group
    rw [this, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g, mul_inv_cancel,
      AlgEquiv.one_apply, hτ'ζ]
  have hζ' : IsPrimitiveRoot (g⁻¹ ζ) (p ^ n) := hζ.map_of_injective (g⁻¹).injective
  have hmod : ℓ ≡ 1 [MOD p ^ n] := by
    have hcop : (p ^ n).Coprime ℓ :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes hp hℓ).2 (Ne.symm hℓp))
    have hpowq := ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ (p ^ n) hA hτ
      hcop (g⁻¹ ζ) hζ'.pow_eq_one
    rw [hτζ'] at hpowq

    have hne : g⁻¹ ζ ≠ 0 := hζ'.ne_zero (pow_ne_zero n hp.ne_zero)
    have h1 : (g⁻¹ ζ) ^ (ℓ - 1) = 1 := by
      have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel hℓ.one_lt.le).symm
      have := hpowq
      rw [hℓ1, pow_succ] at this
      exact (mul_eq_right₀ hne).1 this.symm
    have hdvd : p ^ n ∣ ℓ - 1 := (hζ'.pow_eq_one_iff_dvd _).1 h1
    exact ((Nat.modEq_iff_dvd' hℓ.one_lt.le).2 hdvd).symm

  have hunr : ρbar.IsUnramifiedAt ℓ := by
    intro A' hA' i hi
    exact hHρ i ((hρE i).1 (hunrE A' hA' hi))

  have hpow_eq : ρbar.ρ σ ^ (m * e) = ρbar.ρ σ := by
    have h1 : ρbar.ρ τ' = ρbar.ρ σ ^ m := by rw [hτ'm, map_mul, hHρ h₂ hm2, one_mul, map_pow]
    have h2 : ρbar.ρ τ' ^ e = ρbar.ρ σ := by
      rw [← map_pow, hτ'e, map_mul, hHρ h₁ hm1, one_mul]
    rw [pow_mul, ← h1, h2]
  obtain ⟨hcharm, hscal, hnscal⟩ := charpoly_pow_and ρbar.finrank_eq hαβ hσ m
  have hαβm : α ^ m ≠ β ^ m := by
    intro heq
    have h1 := hscal heq
    apply hnscal ((α ^ m) ^ e)
    rw [← hpow_eq, pow_mul, h1, _root_.smul_pow, one_pow]

  have hfrob : ∀ P : ValuationSubring Qb, P.LiesOverPrime ℓ → ∀ φ : Γ, P.IsFrobeniusAt φ ℓ →
      ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by
    intro P hP φ hφ
    obtain ⟨x, hx⟩ := GlobalGaloisRep.IsUnramifiedAt.exists_apply_eq_apply_conj_of_isFrobeniusAt
      (ρ := ρE) hℓ hunrE hA hP hτ hφ
    obtain ⟨h, hh, hφeq⟩ := modH _ _ hx
    refine ⟨α ^ m, β ^ m, hαβm, ?_⟩
    have hτeq : τ = g⁻¹ * τ' * g := by rw [hτ']; group
    have : ρbar.ρ φ = ρbar.ρ (x * g⁻¹) * ρbar.ρ σ ^ m * ρbar.ρ (x * g⁻¹)⁻¹ := by
      rw [hφeq, map_mul, hHρ h hh, mul_one, hτeq, hτ'm]
      simp only [map_mul, hHρ h₂ hm2, one_mul, map_pow, mul_inv_rev, inv_inv]
      simp only [mul_assoc]
    rw [this]
    exact charpoly_conj_eq ρbar.finrank_eq (by rw [← map_mul, inv_mul_cancel, map_one]) hcharm

  obtain ⟨φ₀, hφ₀⟩ := ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal q
  have hP₀ : (primeLocalPlace q).LiesOverPrime q := ExtCitation.liesOverPrime_primeLocalPlace q
  obtain ⟨x, hx⟩ := GlobalGaloisRep.IsUnramifiedAt.exists_apply_eq_apply_conj_of_isFrobeniusAt
    (ρ := ρE) hℓ hunrE hA hP₀ hτ hφ₀
  obtain ⟨h, hh, hy₀⟩ := modH _ _ hx
  have hnot : ¬ Splits c (primeLocalToGlobal q φ₀) := by
    intro hs
    rw [hy₀, splits_mul_iff (hHM h hh) (hHc0 h hh)] at hs

    have hs1 : Splits c τ := splits_of_isConj (isConj_iff.2 ⟨x⁻¹, by group⟩) hs
    have hs2 : Splits c τ' := splits_of_isConj (isConj_iff.2 ⟨g, hτ'.symm⟩) hs1
    have hs3 : Splits c (τ' ^ e) := splits_pow hs2 e
    rw [hτ'e] at hs3
    obtain ⟨a, ha⟩ := (splits_iff c _).1 hs3
    apply hcσ
    refine ⟨a, ?_⟩
    rw [(mem_cocycles₁_iff c).1 c.2, hHc0 h₁ hm1, add_zero, map_mul, hHM h₁ hm1, one_mul,
      Module.End.one_apply] at ha
    rw [LinearMap.sub_apply, Module.End.one_apply, ha]
  refine ⟨q, hℓT, hmod, hunr, hfrob, map_H1π_ne_zero_of_not_splits _ φ₀ hnot⟩

end P2mCheb
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range.P2mCheb"

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range.P2mCheb"

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {p : ℕ} [Fact p.Prime] {n : ℕ} {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {R : Type} [CommRing R] (M : Rep R (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hM : ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ s ∈ E.fixingSubgroup, M.ρ s = 1)
    (c : cocycles₁ M)
    (hc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s, s ∈ F.fixingSubgroup → c (g * s) = c g)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσζ : σ ζ = ζ)
    {α β : k} (hαβ : α ≠ β) (hσ : LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hcσ : c σ ∉ LinearMap.range (M.ρ σ - 1))
    (T : Finset ℕ) :
    ∃ q : Nat.Primes, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom (H1π M c) ≠ 0 :=
  P2mCheb.main ρbar hζ M hM c hc hσζ hαβ hσ hcσ T

end S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
end P2MW
export P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range (solution)
