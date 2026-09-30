-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_multiplication_fitting
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T00:55:58.618302+00:00
-- url     : https://prove2.me/submissions/bbc81027-f4f3-46c8-adb0-2696a7869537

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section


theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (d : ℕ) (β : Module.Basis (Fin d) ℂ (A ⧸ I))
    (ρ : A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ p : A, ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) :
    ∀ p : A,
      IsCompl (LinearMap.ker ((ρ p) ^ d).mulVecLin)
        (LinearMap.range ((ρ p) ^ d).mulVecLin) ∧
      Nonempty ((A ⧸ I) ≃ₗ[ℂ]
        (LinearMap.ker ((ρ p) ^ d).mulVecLin) ×
          (LinearMap.range ((ρ p) ^ d).mulVecLin)) ∧
      ∀ N : ℕ, d ≤ N →
        LinearMap.ker ((ρ p) ^ N).mulVecLin =
          LinearMap.ker ((ρ p) ^ d).mulVecLin ∧
        LinearMap.range ((ρ p) ^ N).mulVecLin =
          LinearMap.range ((ρ p) ^ d).mulVecLin ∧
        I.colon {p ^ N} = I.colon {p ^ d} := by
  classical
  intro p
  let f : Module.End ℂ (Fin d → ℂ) := (ρ p).mulVecLin
  have hp (n : ℕ) : ((ρ p) ^ n).mulVecLin = f ^ n :=
    Matrix.toLin'_pow (ρ p) n
  have hk (n : ℕ) (hn : d ≤ n) : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ d) := by
    have hdim : Module.finrank ℂ (Fin d → ℂ) = d := by simp
    simpa only [hdim] using
      (Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := f) (hdim.symm ▸ hn))
  have hr (n : ℕ) (hn : d ≤ n) : LinearMap.range (f ^ n) = LinearMap.range (f ^ d) := by
    have hle : LinearMap.range (f ^ n) ≤ LinearMap.range (f ^ d) :=
      f.iterateRange.monotone hn
    apply Submodule.eq_of_le_of_finrank_eq hle
    have h₁ := (f ^ n).finrank_range_add_finrank_ker
    have h₂ := (f ^ d).finrank_range_add_finrank_ker
    rw [hk n hn] at h₁
    exact Nat.add_right_cancel (h₁.trans h₂.symm)
  have hc : IsCompl (LinearMap.ker (f ^ d)) (LinearMap.range (f ^ d)) := by
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
    have h := hn (max d n) (le_max_right d n)
    rwa [hk _ (le_max_left d n), hr _ (le_max_left d n)] at h
  have hmem (n : ℕ) (a : A) :
      β.equivFun (Ideal.Quotient.mk I a) ∈ LinearMap.ker (f ^ n) ↔ a ∈ I.colon {p ^ n} := by
    rw [LinearMap.mem_ker, ← hp, ← map_pow]
    change (ρ (p ^ n)).mulVec (β.equivFun (Ideal.Quotient.mk I a)) = 0 ↔ _
    have haction : (ρ (p ^ n)).mulVec (β.equivFun (Ideal.Quotient.mk I a)) =
        β.equivFun (Ideal.Quotient.mk I (p ^ n * a)) := by
      simp only [Module.Basis.equivFun_apply, hρ,
        Algebra.leftMulMatrix_mulVec_repr, map_mul]
    rw [haction, β.equivFun.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Submodule.mem_colon_singleton, smul_eq_mul, mul_comm a (p ^ n)]
  rw [hp d]
  refine ⟨hc, ⟨β.equivFun.trans (Submodule.prodEquivOfIsCompl _ _ hc).symm⟩, ?_⟩
  intro N hN
  rw [hp N]
  refine ⟨hk N hN, hr N hN, ?_⟩
  ext a
  rw [← hmem N a, ← hmem d a, hk N hN]

