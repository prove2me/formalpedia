-- Prove2me | solution 1 for QuantumInfo.knillLaflamme_of_recovery_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:32.185044+00:00
-- url     : https://prove2.me/submissions/2448863f-59e0-4bfd-b778-dc28df6de21a

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Definitions.Def_KnillLaflammeLean_Basic
public import Theorems.Thm_QuantumInfo_Channel_apply_def
public import Theorems.Thm_QuantumInfo_Channel_id_apply
public import Theorems.Thm_QuantumInfo_exists_smul_of_sum_conj_eq
attribute [local simp] QuantumInfo.Channel.id_apply



set_option autoImplicit false
@[expose] public section
public section
open Matrix
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QuantumInfo
theorem _root_.solution {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ}
    (hP : IsCodeProjector P) {κ : Type*} [Fintype κ] (R : Channel n n κ) (lam : ℂ)
    (h : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (∑ i, E i * ρ * (E i)ᴴ) = lam • ρ) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme P E c := by
  have hscal : ∀ i k, ∃ μ : ℂ, R.kraus k * E i * P = μ • P := by
    intro i k
    refine exists_smul_of_sum_conj_eq hP (fun p : κ × ι => R.kraus p.1 * E p.2 * P) lam
      (fun p => by rw [Matrix.mul_assoc, hP.mul_self]) (fun X => ?_) (k, i)
    have hX : P * X * P = P * (P * X * P) * P := by
      conv_rhs => rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self,
        Matrix.mul_assoc (P * X), hP.mul_self]
    rw [← h (P * X * P) hX, Channel.apply_def, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq]
    simp only [Matrix.mul_assoc]
  choose μ hμ using hscal
  refine ⟨fun i j => ∑ k, star (μ i k) * μ j k, fun i j => ?_⟩
  calc P * (E i)ᴴ * E j * P
      = P * (E i)ᴴ * (∑ k, (R.kraus k)ᴴ * R.kraus k) * E j * P := by
        rw [R.tp, Matrix.mul_one]
    _ = ∑ k, (R.kraus k * E i * P)ᴴ * (R.kraus k * E j * P) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, conjTranspose_mul, hP.conjTranspose_eq,
          Matrix.mul_assoc]
    _ = ∑ k, (star (μ i k) * μ j k) • P := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hμ i k, hμ j k, conjTranspose_smul, hP.conjTranspose_eq, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, hP.mul_self]
    _ = (∑ k, star (μ i k) * μ j k) • P := by rw [Finset.sum_smul]
end QuantumInfo
