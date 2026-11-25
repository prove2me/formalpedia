-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.aug_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:28.484582+00:00
-- url     : https://prove2.me/submissions/2aa72134-1e6d-4083-bc6d-9b5a05832f46

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCartier
import Theorems.Thm_PositivityTheory_PrwZar_Qi_qc_stable
import Theorems.Thm_PositivityTheory_PrwZar_Qi_qc_functional
import Theorems.Thm_PositivityTheory_PrwZar_Qi_qc_leib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution {K H : Type} [Field K] [CharZero K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) :
    RingHom.ker ε ≤ RingHom.ker ε ^ 2 := by
  classical
  intro x hx
  by_contra hx2
  obtain ⟨l, hl1, hl2, hlx⟩ := qc_functional ε hx hx2
  let Φ : H ⊗[K] H →ₗ[K] H := (TensorProduct.rid K H).toLinearMap ∘ₗ LinearMap.lTensor H l
  let mR : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε))
  let mL : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H))
  have hΦ : ∀ s t : H ⊗[K] H, Φ (s * t) = mR s * Φ t + Φ s * mR t := by
    intro s t
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ =>
        simp only [Φ, mR, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul,
          LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply,
          qc_leib ε l hl1 hl2, Algebra.smul_def, map_add, map_mul]
        ring
      | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; ring
    | add s₁ s₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; ring
  have hεΦ : ∀ t : H ⊗[K] H, ε (Φ t) = l (mL t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Φ, mL, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, map_smul, smul_eq_mul]
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | add s t h₁ h₂ => simp only [map_add, h₁, h₂]
  have hRa : ∀ a, mR (Δ a) = a := fun a => DFunLike.congr_fun hR a
  have hLa : ∀ a, mL (Δ a) = a := fun a => DFunLike.congr_fun hL a
  let D : H →ₗ[K] H := Φ ∘ₗ Δ.toLinearMap
  have hD : ∀ a b, D (a * b) = a * D b + D a * b := by
    intro a b
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hΦ, hRa]
  have hεD : ∀ a, ε (D a) = l a := by
    intro a
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hεΦ, hLa]
  have hDpow : ∀ n : ℕ, D (x ^ (n + 1)) = ((n : H) + 1) * x ^ n * D x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hD, ih]
      push_cast
      ring
  obtain ⟨k, hk⟩ := qc_stable (K := K) (RingHom.ker ε)
  have hJJ : RingHom.ker ε ^ (k + 2) * RingHom.ker ε ^ (k + 2) = RingHom.ker ε ^ (k + 2) := by
    rw [← pow_add, hk (k + 2 + (k + 2)) (by omega), hk (k + 2) (by omega)]
  have hDJ : ∀ y ∈ RingHom.ker ε ^ (k + 2), D y ∈ RingHom.ker ε ^ (k + 2) := by
    intro y hy
    rw [← hJJ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [hD]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rw [map_add]
      exact Ideal.add_mem _ ha hb
  have hJ2 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε ^ 2 := Ideal.pow_le_pow_right (by omega)
  have hJ1 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε := Ideal.pow_le_self (by omega)
  have hex : ∃ n, x ^ n ∈ RingHom.ker ε ^ (k + 2) := ⟨k + 2, Ideal.pow_mem_pow hx _⟩
  have hN : x ^ Nat.find hex ∈ RingHom.ker ε ^ (k + 2) := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, x ^ m ∉ RingHom.ker ε ^ (k + 2) := fun m hm => Nat.find_min hex hm
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    have : ε 1 = 0 := hJ1 hN
    simp at this
  have hN1 : Nat.find hex ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hN
    exact hx2 (hJ2 hN)
  obtain ⟨M, hM⟩ : ∃ M, Nat.find hex = M + 2 := ⟨Nat.find hex - 2, by omega⟩
  have h1 : D (x ^ (M + 2)) ∈ RingHom.ker ε ^ (k + 2) := hDJ _ (hM ▸ hN)
  rw [hDpow (M + 1)] at h1
  let π := Ideal.Quotient.mk (RingHom.ker ε ^ (k + 2))
  have hu1 : IsUnit (π ((((M + 1 : ℕ) : H)) + 1)) := by
    have e : π ((((M + 1 : ℕ) : H)) + 1) = algebraMap K (H ⧸ RingHom.ker ε ^ (k + 2)) ((M + 2 : ℕ) : K) := by
      simp only [map_add, map_natCast, map_one]
      push_cast
      ring
    rw [e]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  have hu2 : IsUnit (π (D x)) := by
    have hm : D x - 1 ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker, map_sub, hεD, hlx, map_one, sub_self]
    have hnil : IsNilpotent (π (D x - 1)) :=
      ⟨k + 2, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hm _⟩
    have := hnil.isUnit_one_add
    rwa [map_sub, map_one, add_sub_cancel] at this
  have h0 : π ((((M + 1 : ℕ) : H) + 1) * x ^ (M + 1) * D x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rw [map_mul, map_mul, hu2.mul_left_eq_zero, hu1.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact hmin (M + 1) (by omega) h0
end PositivityTheory.PrwZar.Qi
