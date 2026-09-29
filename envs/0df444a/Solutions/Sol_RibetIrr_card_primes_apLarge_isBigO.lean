-- Prove2me | solution 1 for RibetIrr.card_primes_apLarge_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0585526f-e6c9-587a-be21-c97490038d63

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Fourier.AddCircle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_card_primes_apLarge_isBigO

set_option Elab.async false
set_option autoImplicit false

noncomputable section

namespace RibetIrr
namespace C5

open UpperHalfPlane Complex Real CongruenceSubgroup

variable {M : ℕ} [NeZero M] (g : CuspForm (Gamma0 M) 2)

def horiz (y : ℝ) (hy : 0 < y) : ℝ → ℂ :=
  fun x => g ⟨x + y * Complex.I, by simpa using hy⟩

omit [NeZero M] in

lemma one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

omit [NeZero M] in

lemma continuous_horiz (y : ℝ) (hy : 0 < y) : Continuous (horiz g y hy) := by
  have hg : Continuous (g : ℍ → ℂ) := (ModularFormClass.holo g).continuous
  have hf : Continuous (fun x : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
  exact hg.comp (hf.upperHalfPlaneMk (fun _ => by simpa using hy))

omit [NeZero M] in

lemma norm_horiz_le (y : ℝ) (hy : 0 < y) {C : ℝ}
    (hbd : ∀ τ : UpperHalfPlane, ‖g τ‖ ≤ C / τ.im) (x : ℝ) :
    ‖horiz g y hy x‖ ≤ C / y := by
  have him : (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).im = y := by
    simp [UpperHalfPlane.im, Complex.add_im, Complex.mul_im]
  have := hbd ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩
  rw [him] at this
  exact this

lemma exists_linear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, ‖g τ‖ ≤ C / τ.im := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound g
  refine ⟨max C 0, le_max_right _ _, fun τ => ?_⟩
  calc ‖g τ‖ ≤ C / τ.im ^ ((2 : ℤ) / 2 : ℝ) := hC τ
    _ = C / τ.im := by
        rw [show ((2 : ℤ) / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
    _ ≤ max C 0 / τ.im := by gcongr; exact le_max_left C 0

omit [NeZero M] in

lemma integral_sq_le (y : ℝ) (hy : 0 < y) {C : ℝ} (_hC : 0 ≤ C)
    (hbd : ∀ τ : UpperHalfPlane, ‖g τ‖ ≤ C / τ.im) :
    ∫ x in (0:ℝ)..1, ‖horiz g y hy x‖ ^ 2 ≤ (C / y) ^ 2 := by
  have hpt : ∀ x : ℝ, ‖horiz g y hy x‖ ^ 2 ≤ (C / y) ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_horiz_le g y hy hbd x) 2
  have hint : IntervalIntegrable (fun x => ‖horiz g y hy x‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((continuous_horiz g y hy).norm.pow 2).intervalIntegrable 0 1
  have hconst : IntervalIntegrable (fun _ : ℝ => (C / y) ^ 2) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  calc ∫ x in (0:ℝ)..1, ‖horiz g y hy x‖ ^ 2
      ≤ ∫ _ in (0:ℝ)..1, (C / y) ^ 2 :=
        intervalIntegral.integral_mono zero_le_one hint hconst hpt
    _ = (C / y) ^ 2 := by simp

end RibetIrr.C5

namespace RibetIrr
namespace C5

open UpperHalfPlane Complex Real CongruenceSubgroup MeasureTheory Function

variable {M : ℕ} [NeZero M] (g : CuspForm (Gamma0 M) 2)

lemma fourierCoeffOn_horiz (y : ℝ) (hy : 0 < y) (n : ℕ) :
    fourierCoeffOn (one_pos : (0:ℝ) < 1) (horiz g y hy) (n : ℤ) =
      ModularFormClass.qCoeff (⇑g) n * Real.exp (-(2 * π * n * y)) := by

  have hq := ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := g)
    one_pos (one_mem_strictPeriods_Gamma0 (M := M)) n hy

  have hF := fourierCoeffOn_eq_integral (horiz g y hy) (n : ℤ) (one_pos : (0:ℝ) < 1)

  have hker : ∀ u : ℝ,
      1 / Periodic.qParam 1 (u + y * Complex.I) ^ n *
          g ⟨u + y * Complex.I, by simpa using hy⟩ =
        Complex.exp (2 * π * n * y) *
          (fourier (-(n : ℤ)) (u : AddCircle ((1:ℝ) - 0)) • horiz g y hy u) := by
    intro u
    simp only [horiz, smul_eq_mul, fourier_coe_apply, Periodic.qParam]
    rw [← mul_assoc]
    congr 1
    rw [one_div, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    norm_num
    ring_nf
    simp only [Complex.I_sq]
    ring

  have hqc : ModularFormClass.qCoeff (⇑g) n
      = Complex.exp (2 * π * n * y) *
          fourierCoeffOn (one_pos : (0:ℝ) < 1) (horiz g y hy) (n : ℤ) := by
    show (UpperHalfPlane.qExpansion 1 ⇑g).coeff n = _
    rw [hq, hF, intervalIntegral.integral_congr (fun u _ => hker u),
      intervalIntegral.integral_const_mul]
    norm_num
  rw [hqc, Complex.ofReal_exp]
  rw [mul_comm (Complex.exp _) _, mul_assoc, ← Complex.exp_add]
  rw [show ((2:ℂ) * π * n * y + ↑(-(2 * π * n * y)) : ℂ) = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]

lemma memLp_horiz (y : ℝ) (hy : 0 < y) :
    MemLp (horiz g y hy) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_horiz g y hy).continuousOn
  refine MemLp.of_bound ((continuous_horiz g y hy).aestronglyMeasurable) C₀ ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact ae_of_all _ fun x hx => hC₀ x (Set.Ioc_subset_Icc_self hx)

lemma sum_sq_qCoeff_le (y : ℝ) (hy : 0 < y) (S : Finset ℕ) :
    ∑ n ∈ S, ‖ModularFormClass.qCoeff (⇑g) n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤
      ∫ x in (0:ℝ)..1, ‖horiz g y hy x‖ ^ 2 := by
  have hPar := hasSum_sq_fourierCoeffOn (one_pos : (0:ℝ) < 1) (memLp_horiz g y hy)
  have hone : ((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖horiz g y hy x‖ ^ 2
      = ∫ x in (0:ℝ)..1, ‖horiz g y hy x‖ ^ 2 := by
    norm_num
  rw [hone] at hPar

  have hle := sum_le_hasSum (S.map ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩)
    (fun i _ => by positivity) hPar
  refine le_trans (le_of_eq ?_) hle
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Function.Embedding.coeFn_mk, fourierCoeffOn_horiz g y hy n]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end RibetIrr.C5

namespace RibetIrr
namespace C5

open Real

theorem window_term_lower (a : ℕ → ℝ) {X ℓ : ℕ} (hX4 : 4 ≤ X)
    (hℓmem : ℓ ∈ Finset.Ioc (X / 3) X) (hℓbad : (ℓ : ℝ) - 1 ≤ a ℓ) :
    ((X : ℝ) / 3 - 1) ^ 2 * Real.exp (-(4 * π)) ≤
      a ℓ ^ 2 * Real.exp (-(4 * π * ℓ * (1 / (X : ℝ)))) := by
  rw [Finset.mem_Ioc] at hℓmem
  have hℓlb : (X : ℝ) / 3 - 1 ≤ (ℓ : ℝ) - 1 := by
    have h1 : ((X / 3 : ℕ) : ℝ) + 1 ≤ (ℓ : ℝ) := by exact_mod_cast hℓmem.1
    have hω : X ≤ 3 * (X / 3) + 2 := by omega
    have h2 : (X : ℝ) ≤ 3 * ((X / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast hω
    linarith
  have hℓnn : (0 : ℝ) ≤ (X : ℝ) / 3 - 1 := by
    have : (4 : ℝ) ≤ X := by exact_mod_cast hX4
    linarith
  have hsq : ((X : ℝ) / 3 - 1) ^ 2 ≤ a ℓ ^ 2 := pow_le_pow_left₀ hℓnn (hℓlb.trans hℓbad) 2
  have hexp : Real.exp (-(4 * π)) ≤ Real.exp (-(4 * π * ℓ * (1 / (X : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hℓX : (ℓ : ℝ) ≤ X := by exact_mod_cast hℓmem.2
    have h1 : (ℓ : ℝ) * (1 / X) ≤ 1 := by
      rw [mul_one_div]; exact (div_le_one hXpos).mpr hℓX
    calc 4 * π * ℓ * (1 / (X : ℝ)) = (4 * π) * ((ℓ : ℝ) * (1 / X)) := by ring
      _ ≤ (4 * π) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * π := mul_one _
  exact mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _)

theorem card_le_of_four_le (a : ℕ → ℝ) (C : ℝ) {X : ℕ} (hX4 : 4 ≤ X)
    (hMS : ∀ S : Finset ℕ,
      ∑ n ∈ S, a n ^ 2 * Real.exp (-(4 * π * n * (1 / (X : ℝ)))) ≤ C / (1 / (X : ℝ)) ^ 2) :
    (((Finset.Ioc (X / 3) X).filter fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ a ℓ).card : ℝ) ≤
      144 * C * Real.exp (4 * π) := by
  set S := (Finset.Ioc (X / 3) X).filter fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ a ℓ with hS
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX4' : (4 : ℝ) ≤ X := by exact_mod_cast hX4

  have hCnn : 0 ≤ C := by
    have h := hMS ∅
    rw [Finset.sum_empty] at h
    have hpos : (0 : ℝ) < (1 / (X : ℝ)) ^ 2 := by positivity
    have := (le_div_iff₀ hpos).mp h
    rwa [zero_mul] at this

  have hterm : ∀ ℓ ∈ S, ((X : ℝ) / 3 - 1) ^ 2 * Real.exp (-(4 * π)) ≤
      a ℓ ^ 2 * Real.exp (-(4 * π * ℓ * (1 / (X : ℝ)))) := by
    intro ℓ hℓ
    rw [hS, Finset.mem_filter] at hℓ
    exact window_term_lower a hX4 hℓ.1 hℓ.2.2
  have hsum_lb : (S.card : ℝ) * (((X : ℝ) / 3 - 1) ^ 2 * Real.exp (-(4 * π))) ≤
      ∑ ℓ ∈ S, a ℓ ^ 2 * Real.exp (-(4 * π * ℓ * (1 / (X : ℝ)))) := by
    have := Finset.card_nsmul_le_sum S _ _ hterm
    rwa [nsmul_eq_mul] at this

  have hCX : C / (1 / (X : ℝ)) ^ 2 = C * X ^ 2 := by
    rw [one_div, inv_pow, div_inv_eq_mul]
  have hchain : (S.card : ℝ) * (((X : ℝ) / 3 - 1) ^ 2 * Real.exp (-(4 * π))) ≤ C * X ^ 2 :=
    hsum_lb.trans ((hMS S).trans_eq hCX)

  have hD : (0 : ℝ) < ((X : ℝ) - 3) ^ 2 := pow_pos (by linarith) 2
  have hEpos : (0 : ℝ) < Real.exp (4 * π) := Real.exp_pos _
  have h16 : (X : ℝ) ^ 2 ≤ 16 * ((X : ℝ) - 3) ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 * X - 12 by linarith)
      (show (0 : ℝ) ≤ 5 * X - 12 by linarith)]
  have heq : ((X : ℝ) / 3 - 1) ^ 2 * Real.exp (-(4 * π)) =
      ((X : ℝ) - 3) ^ 2 / 9 * (Real.exp (4 * π))⁻¹ := by
    rw [Real.exp_neg]; ring
  have h2 : (S.card : ℝ) * (((X : ℝ) - 3) ^ 2 / 9 * (Real.exp (4 * π))⁻¹) ≤
      16 * C * ((X : ℝ) - 3) ^ 2 := by
    rw [← heq]
    refine hchain.trans ?_
    calc C * (X : ℝ) ^ 2 ≤ C * (16 * ((X : ℝ) - 3) ^ 2) := mul_le_mul_of_nonneg_left h16 hCnn
      _ = 16 * C * ((X : ℝ) - 3) ^ 2 := by ring
  have hpos : (0 : ℝ) < ((X : ℝ) - 3) ^ 2 / 9 * (Real.exp (4 * π))⁻¹ :=
    mul_pos (div_pos hD (by norm_num)) (inv_pos.mpr hEpos)
  have key : 144 * C * Real.exp (4 * π) * (((X : ℝ) - 3) ^ 2 / 9 * (Real.exp (4 * π))⁻¹) =
      16 * C * ((X : ℝ) - 3) ^ 2 := by
    calc 144 * C * Real.exp (4 * π) * (((X : ℝ) - 3) ^ 2 / 9 * (Real.exp (4 * π))⁻¹)
        = 16 * C * ((X : ℝ) - 3) ^ 2 * (Real.exp (4 * π) * (Real.exp (4 * π))⁻¹) := by ring
      _ = 16 * C * ((X : ℝ) - 3) ^ 2 := by rw [mul_inv_cancel₀ hEpos.ne', mul_one]
  exact le_of_mul_le_mul_right (h2.trans_eq key.symm) hpos

theorem card_window_le (a : ℕ → ℝ) (C : ℝ)
    (hMS : ∀ y : ℝ, 0 < y → ∀ S : Finset ℕ,
      ∑ n ∈ S, a n ^ 2 * Real.exp (-(4 * π * n * y)) ≤ C / y ^ 2) (X : ℕ) :
    ((Finset.Ioc (X / 3) X).filter fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ a ℓ).card ≤
      ⌈144 * C * Real.exp (4 * π)⌉₊ + 3 := by
  rcases lt_or_ge X 4 with hX | hX
  · refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Ioc]
    omega
  · have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hy : (0 : ℝ) < 1 / (X : ℝ) := by positivity
    have h := card_le_of_four_le a C hX (hMS (1 / (X : ℝ)) hy)
    have h' : ((Finset.Ioc (X / 3) X).filter
        fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ a ℓ).card ≤ ⌈144 * C * Real.exp (4 * π)⌉₊ := by
      exact_mod_cast h.trans (Nat.le_ceil _)
    exact h'.trans (Nat.le_add_right _ _)

theorem card_primes_apLarge_of_master {M : ℕ} [NeZero M]
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (hMS : ∃ C : ℝ, ∀ y : ℝ, 0 < y → ∀ S : Finset ℕ,
      ∑ n ∈ S, ‖ModularFormClass.qCoeff (⇑g) n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤ C / y ^ 2) :
    ∃ K : ℕ, ∀ X : ℕ,
      ((Finset.Ioc (X / 3) X).filter
        fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ ‖ModularFormClass.qCoeff g ℓ‖).card ≤ K := by
  obtain ⟨C, hC⟩ := hMS
  exact ⟨_, card_window_le (fun n => ‖ModularFormClass.qCoeff (⇑g) n‖) C hC⟩

end RibetIrr.C5

theorem solution
    (M : ℕ) [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ K : ℕ, ∀ X : ℕ,
      ((Finset.Ioc (X / 3) X).filter
        fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ ‖ModularFormClass.qCoeff g ℓ‖).card ≤ K := by
  obtain ⟨C, hC0, hbd⟩ := RibetIrr.C5.exists_linear_bound g
  exact RibetIrr.C5.card_primes_apLarge_of_master g ⟨C ^ 2, fun y hy S =>
    (RibetIrr.C5.sum_sq_qCoeff_le g y hy S).trans
      ((RibetIrr.C5.integral_sq_le g y hy hC0 hbd).trans_eq (div_pow C y 2))⟩

end

end S_RibetIrr_card_primes_apLarge_isBigO
end P2MW
export P2MW.S_RibetIrr_card_primes_apLarge_isBigO (solution)
