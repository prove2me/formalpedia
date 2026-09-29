-- Prove2me | solution 1 for ResidualGaloisRep.exists_eq_smul_one_of_forall_mul_eq_smul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c198d28e-0034-5490-82a1-6ca2a584e757

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul

set_option autoImplicit false

open TensorProduct

namespace P2mK4NTwist

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section general

variable {K : Type} [Field K] [Algebra k K]
variable {V : Type} [AddCommGroup V] [Module k V]

theorem toMatrix_baseChange_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (Y : Module.End k V) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K b) (Algebra.TensorProduct.basis K b)
      (Y.baseChange K) = (LinearMap.toMatrix b b Y).map (algebraMap k K) :=
  LinearMap.toMatrix_baseChange K Y b b

theorem exists_eq_smul_one_of_baseChange_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (b : Module.Basis ι k V) (Y : Module.End k V) (μ : K)
    (h : Y.baseChange K = μ • (1 : Module.End K (K ⊗[k] V))) :
    ∃ c : k, Y = c • (1 : Module.End k V) ∧ algebraMap k K c = μ := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hM := toMatrix_baseChange_eq (K := K) b Y
  rw [h, LinearEquiv.map_smul, LinearMap.toMatrix_one] at hM

  have hent : ∀ i j, algebraMap k K (LinearMap.toMatrix b b Y i j) =
      (μ • (1 : Matrix ι ι K)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simpa [Matrix.map_apply] using this.symm
  refine ⟨LinearMap.toMatrix b b Y i₀ i₀, ?_, ?_⟩
  · apply (LinearMap.toMatrix b b).injective
    rw [LinearEquiv.map_smul, LinearMap.toMatrix_one]
    ext i j
    have hij := hent i j
    have hii := hent i₀ i₀
    by_cases hd : i = j
    · subst hd
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hij hii ⊢
      apply (algebraMap k K).injective
      rw [hij, hii]
    · simp only [Matrix.smul_apply, Matrix.one_apply_ne hd, smul_eq_mul, mul_zero,
        map_eq_zero] at hij ⊢
      exact hij
  · have hii := hent i₀ i₀
    simpa [Matrix.smul_apply] using hii

theorem eq_zero_of_baseChange_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (b : Module.Basis ι k V) (Y : Module.End k V)
    (h : Y.baseChange K = 0) : Y = 0 := by
  obtain ⟨c, hc, hc0⟩ := exists_eq_smul_one_of_baseChange_eq (K := K) b Y 0
    (by rw [h, zero_smul])
  have : c = 0 := by
    rw [map_eq_zero] at hc0
    exact hc0
  rw [hc, this, zero_smul]

end general

section main

variable (ρbar : ResidualGaloisRep k)

theorem baseChange_ρ_apply (K : Type) [Field K] [Algebra k K] (σ : Γℚ) :
    (ρbar.baseChange K).ρ σ = (ρbar.ρ σ).baseChange K := rfl

variable {ρbar}

theorem exists_baseChange_eq_smul_one
    (K : Type) [Field K] [Algebra k K] [IsAlgClosed K]
    (G : Subgroup Γℚ)
    (hirr : ∀ W : Submodule K (ρbar.baseChange K).V,
      (∀ σ ∈ G, ∀ x ∈ W, (ρbar.baseChange K).ρ σ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (Z : Module.End K (ρbar.baseChange K).V)
    (hZ : ∀ σ ∈ G, Z * (ρbar.baseChange K).ρ σ = (ρbar.baseChange K).ρ σ * Z) :
    ∃ μ : K, Z = μ • (1 : Module.End K (ρbar.baseChange K).V) := by
  haveI : Module.Finite K (ρbar.baseChange K).V := inferInstance
  haveI : Nontrivial (ρbar.baseChange K).V := by
    apply Module.nontrivial_of_finrank_pos (R := K)
    rw [(ρbar.baseChange K).finrank_eq]; norm_num
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue Z
  refine ⟨μ, ?_⟩
  set W : Submodule K (ρbar.baseChange K).V := Z.eigenspace μ with hW
  have hstab : ∀ σ ∈ G, ∀ x ∈ W, (ρbar.baseChange K).ρ σ x ∈ W := by
    intro σ hσ x hx
    rw [hW, Module.End.mem_eigenspace_iff] at hx ⊢
    have h1 : Z ((ρbar.baseChange K).ρ σ x) = (ρbar.baseChange K).ρ σ (Z x) := by
      have := congrArg (fun f : Module.End K (ρbar.baseChange K).V => f x) (hZ σ hσ)
      simpa using this
    rw [h1, hx, map_smul]
  rcases hirr W hstab with hbot | htop
  · exact absurd hbot (Module.End.hasEigenvalue_iff.mp hμ)
  · apply LinearMap.ext
    intro x
    have hx : x ∈ W := by rw [htop]; exact Submodule.mem_top
    rw [hW, Module.End.mem_eigenspace_iff] at hx
    simpa using hx

theorem main (h2 : (2 : k) ≠ 0)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup Γℚ), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (χ : Γℚ →* kˣ) (Y : Module.End k ρbar.V)
    (hY : ∀ σ, Y * ρbar.ρ σ = ((χ σ : kˣ) : k) • (ρbar.ρ σ * Y)) :
    ∃ c : k, Y = c • (1 : Module.End k ρbar.V) ∧ (χ ≠ 1 → c = 0) := by
  classical

  let K : Type := AlgebraicClosure k
  let b : Module.Basis (Fin 2) k ρbar.V := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  set Z : Module.End K (ρbar.baseChange K).V := Y.baseChange K with hZdef
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap k K).injective
    rw [map_ofNat, h, map_zero]

  have hZ' : ∀ σ, Z * (ρbar.baseChange K).ρ σ =
      ((χ σ : kˣ) : k) • ((ρbar.baseChange K).ρ σ * Z) := by
    intro σ
    rw [baseChange_ρ_apply, hZdef, ← LinearMap.baseChange_mul, hY σ, LinearMap.baseChange_smul,
      LinearMap.baseChange_mul]
  have hZ : ∀ σ, Z * (ρbar.baseChange K).ρ σ =
      (algebraMap k K ((χ σ : kˣ) : k)) • ((ρbar.baseChange K).ρ σ * Z) := by
    intro σ
    rw [hZ' σ, algebraMap_smul]

  by_cases hχ : χ = 1
  ·
    have hcomm : ∀ σ ∈ (⊤ : Subgroup Γℚ), Z * (ρbar.baseChange K).ρ σ =
        (ρbar.baseChange K).ρ σ * Z := by
      intro σ _
      rw [hZ σ, hχ]
      simp
    have hirr : ∀ W : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ (⊤ : Subgroup Γℚ), ∀ x ∈ W, (ρbar.baseChange K).ρ σ x ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      exact habs W (fun σ x hx => hW σ (Subgroup.mem_top σ) x hx)
    obtain ⟨μ, hμ⟩ := exists_baseChange_eq_smul_one K ⊤ hirr Z hcomm
    obtain ⟨c, hc, -⟩ := exists_eq_smul_one_of_baseChange_eq (K := K) b Y μ (by rw [← hZdef, hμ])
    exact ⟨c, hc, fun h => absurd hχ h⟩
  ·
    suffices hY0 : Y = 0 by exact ⟨0, by rw [hY0, zero_smul], fun _ => rfl⟩

    by_cases hdet : LinearMap.det Z = 0
    ·
      have hker : LinearMap.ker Z ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
      have hstab : ∀ σ : Γℚ, ∀ x ∈ LinearMap.ker Z, (ρbar.baseChange K).ρ σ x ∈ LinearMap.ker Z := by
        intro σ x hx
        rw [LinearMap.mem_ker] at hx ⊢
        have := congrArg (fun f : Module.End K (ρbar.baseChange K).V => f x) (hZ σ)
        simp only [Module.End.mul_apply, LinearMap.smul_apply, hx, map_zero, smul_zero] at this
        exact this
      rcases habs (LinearMap.ker Z) hstab with hbot | htop
      · exact absurd hbot hker
      · have hZ0 : Z = 0 := LinearMap.ker_eq_top.mp htop
        exact eq_zero_of_baseChange_eq_zero (K := K) b Y (by rw [← hZdef, hZ0])
    ·
      have hsq : ∀ σ, ((χ σ : kˣ) : k) ^ 2 = 1 := by
        intro σ
        have hdetρ : LinearMap.det ((ρbar.baseChange K).ρ σ) ≠ 0 := by
          have hu : IsUnit ((ρbar.baseChange K).ρ σ) := by
            refine ⟨⟨(ρbar.baseChange K).ρ σ, (ρbar.baseChange K).ρ σ⁻¹, ?_, ?_⟩, rfl⟩
            · rw [← map_mul, mul_inv_cancel, map_one]
            · rw [← map_mul, inv_mul_cancel, map_one]
          exact (LinearMap.isUnit_det _ hu).ne_zero
        have hd := congrArg LinearMap.det (hZ σ)
        rw [map_mul, LinearMap.det_smul, map_mul, (ρbar.baseChange K).finrank_eq] at hd

        have h' : (algebraMap k K ((χ σ : kˣ) : k)) ^ 2 = 1 := by
          have hne : LinearMap.det ((ρbar.baseChange K).ρ σ) * LinearMap.det Z ≠ 0 :=
            mul_ne_zero hdetρ hdet
          rw [mul_comm (LinearMap.det Z) (LinearMap.det ((ρbar.baseChange K).ρ σ))] at hd
          have : (1 : K) * (LinearMap.det ((ρbar.baseChange K).ρ σ) * LinearMap.det Z) =
              (algebraMap k K ((χ σ : kˣ) : k)) ^ 2 *
                (LinearMap.det ((ρbar.baseChange K).ρ σ) * LinearMap.det Z) := by
            rw [one_mul]
            exact hd
          exact (mul_right_cancel₀ hne this).symm
        apply (algebraMap k K).injective
        rw [map_pow, h', map_one]

      have hpm : ∀ σ, ((χ σ : kˣ) : k) = 1 ∨ ((χ σ : kˣ) : k) = -1 := fun σ =>
        sq_eq_one_iff.mp (hsq σ)

      obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, χ σ₀ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hχ (MonoidHom.ext hcon)
      have hσ₀' : ((χ σ₀ : kˣ) : k) = -1 := by
        rcases hpm σ₀ with h | h
        · exact absurd (Units.val_eq_one.mp h) hσ₀
        · exact h

      have hindex : χ.ker.index = 2 := by
        rw [Subgroup.index_eq_two_iff_exists_notMem_and]
        refine ⟨σ₀, ?_, fun τ => ?_⟩
        · rwa [MonoidHom.mem_ker]
        · rcases hpm τ with h | h
          · right
            rw [MonoidHom.mem_ker]
            exact Units.val_eq_one.mp h
          · left
            rw [MonoidHom.mem_ker, ← Units.val_eq_one, map_mul, Units.val_mul, h, hσ₀']
            ring

      have hcomm : ∀ σ ∈ χ.ker, Z * (ρbar.baseChange K).ρ σ = (ρbar.baseChange K).ρ σ * Z := by
        intro σ hσ
        rw [MonoidHom.mem_ker] at hσ
        rw [hZ σ, hσ]
        simp
      obtain ⟨μ, hμ⟩ := exists_baseChange_eq_smul_one K χ.ker (hTW K χ.ker hindex) Z hcomm

      have hrel := hZ σ₀
      rw [hσ₀', hμ, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, map_neg, map_one,
        neg_smul, one_smul] at hrel

      have hρne : (ρbar.baseChange K).ρ σ₀ ≠ 0 := by
        haveI : Nontrivial (ρbar.baseChange K).V := by
          apply Module.nontrivial_of_finrank_pos (R := K)
          rw [(ρbar.baseChange K).finrank_eq]; norm_num
        intro h0
        have h1 : (ρbar.baseChange K).ρ σ₀ * (ρbar.baseChange K).ρ σ₀⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      have h2μ : (2 * μ) • (ρbar.baseChange K).ρ σ₀ = 0 := by
        rw [mul_smul, two_smul]
        nth_rewrite 1 [hrel]
        rw [neg_add_cancel]
      have hμ0 : μ = 0 := by
        rcases smul_eq_zero.mp h2μ with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' h2K
          · exact h'
        · exact absurd h hρne
      rw [hμ0, zero_smul] at hμ
      exact eq_zero_of_baseChange_eq_zero (K := K) b Y (by rw [← hZdef, hμ])

end main

end P2mK4NTwist

theorem solution
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (Y : Module.End k ρbar.V)
    (hY : ∀ σ, Y * ρbar.ρ σ = ((χ σ : kˣ) : k) • (ρbar.ρ σ * Y)) :
    ∃ c : k, Y = c • (1 : Module.End k ρbar.V) ∧ (χ ≠ 1 → c = 0) :=
  P2mK4NTwist.main h2 habs hTW χ Y hY

end S_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul
end P2MW
export P2MW.S_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul (solution)
