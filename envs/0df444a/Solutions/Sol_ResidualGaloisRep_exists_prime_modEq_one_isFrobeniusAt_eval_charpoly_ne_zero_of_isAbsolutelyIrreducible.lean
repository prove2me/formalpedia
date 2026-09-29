-- Prove2me | solution 1 for ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6373b149-6550-5c91-908a-3f204e72f9f0

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

namespace EscompEis

open Module Polynomial

section LinearAlgebra

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

lemma apply_basis_eq (b : Basis (Fin 2) K V) (f : V →ₗ[K] V) (j : Fin 2) :
    f (b j) = (LinearMap.toMatrix b b f) 0 j • b 0 + (LinearMap.toMatrix b b f) 1 j • b 1 := by
  have h := (b.sum_repr (f (b j))).symm
  rw [Fin.sum_univ_two] at h
  simpa [LinearMap.toMatrix_apply] using h

lemma matrix_rel_of_fixed (b : Basis (Fin 2) K V) (f : V →ₗ[K] V) {v : V} (hv : v ≠ 0)
    (hfv : f v = v) :
    (LinearMap.toMatrix b b f 0 0 - 1) * (LinearMap.toMatrix b b f 1 1 - 1)
      - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 = 0 := by
  classical
  have hd : (LinearMap.toMatrix b b (f - 1)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨b.repr v, ?_, ?_⟩
    · intro h0
      apply hv
      have : b.repr v = 0 := Finsupp.ext fun i => by simpa using congrFun h0 i
      simpa using this
    · rw [LinearMap.toMatrix_mulVec_repr]
      ext i
      simp [hfv]
  rw [map_sub, LinearMap.toMatrix_one, Matrix.det_fin_two] at hd
  simpa [Matrix.sub_apply, Matrix.one_apply] using hd

lemma line_ne_bot {v : V} (hv : v ≠ 0) : (K ∙ v) ≠ ⊥ := fun h =>
  hv ((Submodule.span_singleton_eq_bot).mp h)

lemma line_ne_top (h2 : finrank K V = 2) {v : V} (hv : v ≠ 0) : (K ∙ v) ≠ ⊤ := by
  intro h
  have h1 : finrank K (K ∙ v) = 1 := finrank_span_singleton hv
  rw [h, finrank_top] at h1
  omega

theorem stable_line_or_commute (h2 : finrank K V = 2) {G : Type*} [Group G]
    (ρ : G →* Module.End K V) (H : Subgroup G)
    (hnorm : ∀ g h : G, h ∈ H → g * h * g⁻¹ ∈ H)
    (hcommH : ∀ g g' : G, g * g' * g⁻¹ * g'⁻¹ ∈ H)
    (hfix : ∀ h ∈ H, LinearMap.det (ρ h) = 1 → ∃ v : V, v ≠ 0 ∧ ρ h v = v) :
    (∃ L : Submodule K V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ g, ∀ v ∈ L, ρ g v ∈ L) ∨
      (∀ g g' : G, ρ g * ρ g' = ρ g' * ρ g) := by
  classical
  haveI : Module.Finite K V := Module.finite_of_finrank_eq_succ h2
  have hinv : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  by_cases hK : ∃ h₀ ∈ H, LinearMap.det (ρ h₀) = 1 ∧ ρ h₀ ≠ 1
  ·
    left
    obtain ⟨g₀, hg₀H, hdet₀, hne⟩ := hK
    obtain ⟨v₀, hv₀, hfix₀⟩ := hfix g₀ hg₀H hdet₀
    obtain ⟨w, hw⟩ : ∃ w : V, w ∉ (K ∙ v₀) := by
      by_contra hall
      push Not at hall
      exact line_ne_top h2 hv₀ (Submodule.eq_top_iff'.mpr hall)
    have hli : LinearIndependent K ![v₀, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero, smul_eq_zero] at hst
        exact ⟨hst.resolve_right hv₀, rfl⟩
      · exfalso
        apply hw
        rw [Submodule.mem_span_singleton]
        refine ⟨-(s / t), ?_⟩
        have : t • w = -(s • v₀) := eq_neg_of_add_eq_zero_right hst
        calc -(s / t) • v₀ = t⁻¹ • (-(s • v₀)) := by rw [smul_neg, smul_smul, neg_smul]; ring_nf
          _ = t⁻¹ • (t • w) := by rw [this]
          _ = w := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    let b : Basis (Fin 2) K V :=
      basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
    have hb0 : b 0 = v₀ := by simp [b]
    set Am : G → Matrix (Fin 2) (Fin 2) K := fun g => LinearMap.toMatrix b b (ρ g) with hAm
    have Amul : ∀ g h, Am (g * h) = Am g * Am h := by
      intro g h; simp only [Am, map_mul, LinearMap.toMatrix_mul]
    have Adet : ∀ g, Am g 0 0 * Am g 1 1 - Am g 0 1 * Am g 1 0 = LinearMap.det (ρ g) := by
      intro g; rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    have Afix : ∀ g ∈ H, LinearMap.det (ρ g) = 1 →
        (Am g 0 0 - 1) * (Am g 1 1 - 1) - Am g 0 1 * Am g 1 0 = 0 := by
      intro g hgH hg
      obtain ⟨v, hv, hv'⟩ := hfix g hgH hg
      exact matrix_rel_of_fixed b (ρ g) hv hv'

    have hρb0 : ρ g₀ (b 0) = b 0 := by rw [hb0]; exact hfix₀
    have h00 : Am g₀ 0 0 = 1 := by simp [Am, LinearMap.toMatrix_apply, hρb0]
    have h10 : Am g₀ 1 0 = 0 := by simp [Am, LinearMap.toMatrix_apply, hρb0]
    have h11 : Am g₀ 1 1 = 1 := by
      have := Adet g₀; rw [h00, h10, hdet₀] at this; linear_combination this
    have hβ : Am g₀ 0 1 ≠ 0 := by
      intro h01
      apply hne
      have : Am g₀ = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
      have h1 : LinearMap.toMatrix b b (ρ g₀) = LinearMap.toMatrix b b 1 := by
        rw [LinearMap.toMatrix_one]; exact this
      exact (LinearMap.toMatrix b b).injective h1

    have hunip : ∀ g ∈ H, LinearMap.det (ρ g) = 1 →
        Am g 1 0 = 0 ∧ Am g 0 0 = 1 ∧ Am g 1 1 = 1 := by
      intro g hgH hg
      have e1 := Afix g hgH hg
      have e2 := Adet g
      rw [hg] at e2

      have hg₀gH : g₀ * g ∈ H := H.mul_mem hg₀H hgH
      have hg₀g : LinearMap.det (ρ (g₀ * g)) = 1 := by
        rw [map_mul, map_mul, hdet₀, hg, one_mul]
      have e3 := Afix (g₀ * g) hg₀gH hg₀g
      have e4 := Adet (g₀ * g)
      rw [hg₀g] at e4
      have p00 : Am (g₀ * g) 0 0 = Am g 0 0 + Am g₀ 0 1 * Am g 1 0 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h00]
      have p11 : Am (g₀ * g) 1 1 = Am g 1 1 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
      have p01 : Am (g₀ * g) 0 1 = Am g 0 1 + Am g₀ 0 1 * Am g 1 1 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h00]
      have p10 : Am (g₀ * g) 1 0 = Am g 1 0 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
      rw [p00, p11, p01, p10] at e3 e4

      have htr1 : Am g 0 0 + Am g 1 1 = 2 := by linear_combination e2 - e1
      have htr2 : Am g 0 0 + Am g₀ 0 1 * Am g 1 0 + Am g 1 1 = 2 := by
        linear_combination e4 - e3
      have hc0 : Am g 1 0 = 0 := by
        have : Am g₀ 0 1 * Am g 1 0 = 0 := by linear_combination htr2 - htr1
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hβ
        · exact h
      have ha : Am g 0 0 = 1 := by
        have hsq : (Am g 0 0 - 1) ^ 2 = 0 := by
          rw [hc0] at e2
          linear_combination (Am g 0 0) * htr1 - e2
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        linear_combination this
      refine ⟨hc0, ha, ?_⟩
      linear_combination htr1 - ha

    have hupper : ∀ g, Am g 1 0 = 0 := by
      intro g
      have hkH : g * g₀ * g⁻¹ ∈ H := hnorm g g₀ hg₀H
      have hk : LinearMap.det (ρ (g * g₀ * g⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_mul, hdet₀, mul_one, ← map_mul, hinv, map_one]
      obtain ⟨k10, k00, k11⟩ := hunip _ hkH hk
      have hprod : Am (g * g₀ * g⁻¹) * Am g = Am g * Am g₀ := by
        rw [← Amul, ← Amul]
        congr 1
        group
      have := congrFun (congrFun hprod 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, k10, k11, h11, zero_mul, one_mul,
        zero_add, mul_one] at this

      have h0 : Am g 1 0 * Am g₀ 0 1 = 0 := by linear_combination -this
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hβ
    refine ⟨K ∙ v₀, line_ne_bot hv₀, line_ne_top h2 hv₀, ?_⟩
    intro g v hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := apply_basis_eq b (ρ g) 0
    rw [hb0] at this
    rw [this, show LinearMap.toMatrix b b (ρ g) 1 0 = Am g 1 0 from rfl, hupper g, zero_smul,
      add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₀)
  ·
    right
    push Not at hK
    intro g h
    have hcH : g * h * g⁻¹ * h⁻¹ ∈ H := hcommH g h
    have h1 : LinearMap.det (ρ (g * h * g⁻¹ * h⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
        mul_comm (LinearMap.det (ρ g)) (LinearMap.det (ρ h)), mul_assoc, mul_assoc,
        ← mul_assoc (LinearMap.det (ρ g)), ← map_mul, hinv, map_one, one_mul, ← map_mul,
        hinv, map_one]
    have h2' := hK _ hcH h1
    calc ρ g * ρ h = ρ (g * h) := (map_mul ρ g h).symm
      _ = ρ (g * h * g⁻¹ * h⁻¹ * (h * g)) := by congr 1; group
      _ = ρ (g * h * g⁻¹ * h⁻¹) * ρ (h * g) := map_mul ρ _ _
      _ = ρ h * ρ g := by rw [h2', one_mul, map_mul]

theorem false_of_irreducible [IsAlgClosed K] (h2 : finrank K V = 2) {G : Type*} [Group G]
    (ρ : G →* Module.End K V)
    (hirr : ∀ W : Submodule K V, (∀ g : G, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (h : (∃ L : Submodule K V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ g, ∀ v ∈ L, ρ g v ∈ L) ∨
      (∀ g g' : G, ρ g * ρ g' = ρ g' * ρ g)) : False := by
  classical
  haveI : Module.Finite K V := Module.finite_of_finrank_eq_succ h2
  rcases h with ⟨L, hLbot, hLtop, hLstab⟩ | hcomm
  · rcases hirr L hLstab with h | h
    · exact hLbot h
    · exact hLtop h
  · have hpos : 0 < finrank K V := by omega
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)

    have hscal : ∀ g, ∃ c : K, ρ g = c • (1 : Module.End K V) := by
      intro g₁
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ g₁)
      refine ⟨μ, ?_⟩
      have hstab : ∀ g : G, ∀ x ∈ (ρ g₁).eigenspace μ, ρ g x ∈ (ρ g₁).eigenspace μ := by
        intro g v hv
        rw [Module.End.mem_eigenspace_iff] at hv ⊢
        have := congrArg (fun f => f v) (hcomm g₁ g)
        simp only [Module.End.mul_apply] at this
        rw [this, hv, map_smul]
      rcases hirr _ hstab with hbot | htop
      · exact absurd hbot (Module.End.hasEigenvalue_iff.mp hμ)
      · ext v
        have hv : v ∈ (ρ g₁).eigenspace μ := htop ▸ Submodule.mem_top
        rw [Module.End.mem_eigenspace_iff] at hv
        rw [hv, LinearMap.smul_apply, Module.End.one_apply]

    have hstab : ∀ g : G, ∀ x ∈ (K ∙ v₁), ρ g x ∈ (K ∙ v₁) := by
      intro g x hx
      obtain ⟨c, hc⟩ := hscal g
      rw [hc, LinearMap.smul_apply, Module.End.one_apply]
      exact Submodule.smul_mem _ _ hx
    rcases hirr _ hstab with h | h
    · exact line_ne_bot hv₁ h
    · exact line_ne_top h2 hv₁ h

end LinearAlgebra

section Cyclotomic

local notation "Qb" => AlgebraicClosure ℚ

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def muFix (N : ℕ) : Subgroup Γ where
  carrier := {σ | ∀ ζ : Qb, ζ ^ N = 1 → σ ζ = ζ}
  one_mem' := by intro ζ _; rfl
  mul_mem' := by
    intro σ τ hσ hτ ζ hζ
    show (σ * τ) ζ = ζ
    rw [AlgEquiv.mul_apply, hτ ζ hζ, hσ ζ hζ]
  inv_mem' := by
    intro σ hσ ζ hζ
    show σ⁻¹ ζ = ζ
    rw [AlgEquiv.aut_inv]
    conv_lhs => rw [← hσ ζ hζ]
    exact σ.symm_apply_apply ζ

lemma mem_muFix_iff {N : ℕ} (σ : Γ) : σ ∈ muFix N ↔ ∀ ζ : Qb, ζ ^ N = 1 → σ ζ = ζ := Iff.rfl

private lemma _root_.EscompEis.exists_isPrimitiveRoot (N : ℕ) [NeZero N] : ∃ ζ₀ : Qb, IsPrimitiveRoot ζ₀ N :=
  IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({N} : Set ℕ)) Qb Qb
    (Set.mem_singleton N) (NeZero.ne N)

p2m_export "EscompEis" "exists_isPrimitiveRoot"
lemma pow_N_map {N : ℕ} (g : Γ) {ζ : Qb} (hζ : ζ ^ N = 1) : (g ζ) ^ N = 1 := by
  rw [← map_pow, hζ, map_one]

lemma exists_pow_action (N : ℕ) [NeZero N] (g : Γ) :
    ∃ a : ℕ, ∀ ζ : Qb, ζ ^ N = 1 → g ζ = ζ ^ a := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot N
  obtain ⟨a, -, ha⟩ := hζ₀.eq_pow_of_pow_eq_one (pow_N_map g hζ₀.pow_eq_one)
  refine ⟨a, fun ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

lemma apply_apply_comm (N : ℕ) [NeZero N] (g g' : Γ) {ζ : Qb} (hζ : ζ ^ N = 1) :
    g (g' ζ) = g' (g ζ) := by
  obtain ⟨a, ha⟩ := exists_pow_action N g
  obtain ⟨a', ha'⟩ := exists_pow_action N g'
  rw [ha' ζ hζ, map_pow, ha ζ hζ, map_pow, ha' ζ hζ, ← pow_mul, ← pow_mul, mul_comm]

lemma inv_apply_pow_N {N : ℕ} (g : Γ) {ζ : Qb} (hζ : ζ ^ N = 1) : (g⁻¹ ζ) ^ N = 1 :=
  pow_N_map g⁻¹ hζ

lemma apply_inv_apply (g : Γ) (x : Qb) : g (g⁻¹ x) = x := by
  rw [AlgEquiv.aut_inv]; exact g.apply_symm_apply x

lemma inv_apply_apply (g : Γ) (x : Qb) : g⁻¹ (g x) = x := by
  rw [AlgEquiv.aut_inv]; exact g.symm_apply_apply x

lemma muFix_normal (N : ℕ) (g h : Γ) (hh : h ∈ muFix N) : g * h * g⁻¹ ∈ muFix N := by
  intro ζ hζ
  show (g * h * g⁻¹) ζ = ζ
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh _ (inv_apply_pow_N g hζ), apply_inv_apply]

lemma commutator_mem_muFix (N : ℕ) [NeZero N] (g g' : Γ) :
    g * g' * g⁻¹ * g'⁻¹ ∈ muFix N := by
  intro ζ hζ
  show (g * g' * g⁻¹ * g'⁻¹) ζ = ζ
  have hx : (g⁻¹ (g'⁻¹ ζ)) ^ N = 1 := inv_apply_pow_N g (inv_apply_pow_N g' hζ)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    apply_apply_comm N g g' hx, apply_inv_apply, apply_inv_apply]

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

lemma isOpen_muFix (N : ℕ) [NeZero N] : IsOpen ((muFix N : Subgroup Γ) : Set Γ) := by
  haveI := isIntegral_algebraicClosure_rat
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot N
  apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer Γ ζ₀)
  · intro σ hσ ζ hζ
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hσ
    obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
    show σ (ζ₀ ^ i) = ζ₀ ^ i
    rw [map_pow, hσ]
  · exact stabilizer_isOpen_of_isIntegral ζ₀

lemma modEq_one_of_conj_mem_muFix (N : ℕ) [NeZero N] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    {A : ValuationSubring Qb} {τ : Γ} (hA : A.LiesOverPrime ℓ) (hτ : A.IsFrobeniusAt τ ℓ)
    (g : Γ) (hg : g * τ * g⁻¹ ∈ muFix N) : ℓ ≡ 1 [MOD N] := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot N

  set ζ' : Qb := g⁻¹ ζ₀ with hζ'def
  have hζ' : IsPrimitiveRoot ζ' N := hζ₀.map_of_injective (f := (g⁻¹ : Γ)) (g⁻¹).injective
  have hfixζ' : τ ζ' = ζ' := by
    have h1 : (g * τ * g⁻¹) ζ₀ = ζ₀ := hg ζ₀ hζ₀.pow_eq_one
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h1
    have h2 := congrArg (g⁻¹ : Γ) h1
    rwa [inv_apply_apply] at h2

  have hcop : N.Coprime ℓ := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))
  have hpow : τ ζ' = ζ' ^ ℓ :=
    ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ N hA hτ hcop ζ' hζ'.pow_eq_one
  have hone : ζ' ^ (ℓ - 1) = 1 := by
    have hne : ζ' ≠ 0 := hζ'.ne_zero (NeZero.ne N)
    have : ζ' ^ (ℓ - 1) * ζ' = 1 * ζ' := by
      rw [pow_sub_one_mul hℓ.ne_zero, one_mul, ← hpow, hfixζ']
    exact mul_right_cancel₀ hne this
  have hdvd : N ∣ ℓ - 1 := (hζ'.pow_eq_one_iff_dvd _).mp hone
  exact ((Nat.modEq_iff_dvd' hℓ.one_lt.le).mpr hdvd).symm

end Cyclotomic

theorem main {k : Type} [Field k] (ρ : ResidualGaloisRep k) (hρ : ρ.IsAbsolutelyIrreducible)
    (N : ℕ) [NeZero N] {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ≡ 1 [MOD N] ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        (LinearMap.charpoly (ρ.ρ σ)).eval 1 ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon

  let K := AlgebraicClosure k
  let ρ' : ResidualGaloisRep K := ρ.baseChange K
  have hirr : ρ'.IsIrreducible := hρ
  have hρ'apply : ∀ σ, ρ'.ρ σ = (ρ.ρ σ).baseChange K := fun σ => rfl
  have h2 : finrank K ρ'.V = 2 := ρ'.finrank_eq
  haveI : Module.Finite K ρ'.V := Module.finite_of_finrank_eq_succ h2

  obtain ⟨L, hLfd, hL⟩ := ρ'.factorsThroughFiniteLevel
  haveI := hLfd
  have hUopen : IsOpen (((L.fixingSubgroup ⊓ muFix N : Subgroup _)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    (IntermediateField.fixingSubgroup_isOpen L).inter (isOpen_muFix N)
  have hinv : ∀ g, ρ'.ρ g * ρ'.ρ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]

  have hfix : ∀ σ ∈ muFix N, LinearMap.det (ρ'.ρ σ) = 1 →
      ∃ v : ρ'.V, v ≠ 0 ∧ ρ'.ρ σ v = v := by
    intro σ hσ _
    have hMN : 0 < M * N := Nat.mul_pos hM (Nat.pos_of_ne_zero (NeZero.ne N))
    obtain ⟨ℓ, A, τ, g, n, κ, hℓ, hℓMN, hA, hτ, hmem, hmem'⟩ :=
      (L.fixingSubgroup ⊓ muFix N).exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
        hUopen σ hMN
    have hℓM : ¬ ℓ ∣ M := fun h => hℓMN (h.mul_right N)
    have hℓN : ¬ ℓ ∣ N := fun h => hℓMN (h.mul_left M)

    have hgτg : g * τ * g⁻¹ ∈ muFix N := by
      have h1 : g * τ * g⁻¹ * (σ ^ κ)⁻¹ ∈ muFix N := (Subgroup.mem_inf.mp hmem').2
      have h2 : σ ^ κ ∈ muFix N := Subgroup.pow_mem _ hσ κ
      have := Subgroup.mul_mem _ h1 h2
      rwa [inv_mul_cancel_right] at this
    have hmod : ℓ ≡ 1 [MOD N] := modEq_one_of_conj_mem_muFix N hℓ hℓN hA hτ g hgτg

    have heval : (LinearMap.charpoly (ρ.ρ τ)).eval 1 = 0 := hcon ℓ A τ hℓ hℓM hmod hA hτ
    have heval' : (LinearMap.charpoly (ρ'.ρ τ)).IsRoot 1 := by
      rw [hρ'apply, LinearMap.charpoly_baseChange, IsRoot.def, eval_one_map, heval, map_zero]
    have hev : (ρ'.ρ τ).HasEigenvalue 1 :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr heval'
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hv0 : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
    have hτv : ρ'.ρ τ v = v := by rw [hv.apply_eq_smul, one_smul]

    have hker : ρ'.ρ (g * τ ^ n * g⁻¹ * σ⁻¹) = 1 :=
      hL _ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff L _).mp
        (Subgroup.mem_inf.mp hmem).1 x hx)
    have hστ : ρ'.ρ σ = ρ'.ρ g * ρ'.ρ τ ^ n * ρ'.ρ g⁻¹ := by
      have h2' : ρ'.ρ (g * τ ^ n * g⁻¹) = ρ'.ρ σ := by
        calc ρ'.ρ (g * τ ^ n * g⁻¹) = ρ'.ρ (g * τ ^ n * g⁻¹ * σ⁻¹ * σ) := by congr 1; group
          _ = ρ'.ρ σ := by rw [map_mul, hker, one_mul]
      rw [← h2', map_mul, map_mul, map_pow]
    have hginv : ∀ x : ρ'.V, ρ'.ρ g⁻¹ (ρ'.ρ g x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hτn : (ρ'.ρ τ ^ n) v = v := by
      rw [Module.End.pow_apply]
      exact Function.iterate_fixed hτv n
    refine ⟨ρ'.ρ g v, ?_, ?_⟩
    · intro h0
      apply hv0
      rw [← hginv v, h0, _root_.map_zero]
    · rw [hστ, Module.End.mul_apply, Module.End.mul_apply, hginv, hτn]

  have hdisj := stable_line_or_commute h2 ρ'.ρ (muFix N) (muFix_normal N)
    (commutator_mem_muFix N) hfix
  exact false_of_irreducible h2 ρ'.ρ hirr hdisj

end EscompEis

theorem solution
    {k : Type} [Field k] (ρ : ResidualGaloisRep k) (hρ : ρ.IsAbsolutelyIrreducible)
    (N : ℕ) [NeZero N] {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ≡ 1 [MOD N] ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        (LinearMap.charpoly (ρ.ρ σ)).eval 1 ≠ 0 :=
  EscompEis.main ρ hρ N hM

end S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible (solution)
