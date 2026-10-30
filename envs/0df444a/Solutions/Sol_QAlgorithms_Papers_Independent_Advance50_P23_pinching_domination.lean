-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P23.pinching_domination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:34:33.007089+00:00
-- url     : https://prove2.me/submissions/01699715-2fec-4623-9362-831133b94ab1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

end QAlgorithms.Papers.Independent.Advance50.P23

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P23 Matrix
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

lemma s110pd_card {E : Type} [Fintype E] [DecidableEq E] (sigma : Matrix E E ℂ)
    (h : sigma.IsHermitian) :
    eigenCount sigma = (Finset.univ.image h.eigenvalues).card := by
  unfold eigenCount ascEigenvalues
  rw [dif_pos h]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) k.rev, ?_⟩
    simp [Matrix.IsHermitian.eigenvalues]
  · rintro ⟨k, rfl⟩
    refine ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k).rev, ?_⟩
    simp [Matrix.IsHermitian.eigenvalues]

theorem solution {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (rho sigma : Matrix E E ℂ) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef) :
    (((eigenCount sigma : ℂ) • pinch sigma rho) - rho).PosSemidef := by
  have h : sigma.IsHermitian := hsigma.1
  set L := Finset.univ.image h.eigenvalues with hL
  set P : ℝ → Matrix E E ℂ := fun l => cfc (fun x : ℝ => if x = l then 1 else 0) sigma with hP
  have hpinch : pinch sigma rho = ∑ l ∈ L, P l * rho * P l := by
    unfold pinch
    rw [dif_pos h]
  have hPH : ∀ l, (P l)ᴴ = P l := by
    intro l
    have : IsSelfAdjoint (P l) := cfc_predicate _ _
    exact this
  have hsum : ∑ l ∈ L, P l = 1 := by
    have hsa : IsSelfAdjoint sigma := h
    have hfin : (spectrum ℝ sigma).Finite := Matrix.finite_real_spectrum
    rw [hP]
    simp only
    rw [← cfc_sum (hf := fun i _ => hfin.continuousOn _)]
    rw [← cfc_one ℝ sigma]
    apply cfc_congr
    intro x hx
    rw [h.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨k, rfl⟩ := hx
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single (h.eigenvalues k)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hk; exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ k)) hk
  have hcard : (eigenCount sigma : ℂ) = (L.card : ℂ) := by rw [s110pd_card sigma h]
  have key : ∑ l ∈ L, ∑ m ∈ L, (P l - P m) * rho * (P l - P m)ᴴ =
      (2 : ℂ) • (((eigenCount sigma : ℂ) • pinch sigma rho) - rho) := by
    simp only [conjTranspose_sub, hPH]
    have e : ∀ l m, (P l - P m) * rho * (P l - P m) =
        P l * rho * P l + P m * rho * P m - (P l * rho * P m + P m * rho * P l) := by
      intro l m; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, hpinch, hcard]
    have h1 : ∑ l ∈ L, ∑ m ∈ L, P l * rho * P m = rho := by
      simp only [← Matrix.mul_sum, ← Finset.sum_mul, hsum, Matrix.mul_one, Matrix.one_mul]
    have h2 : ∑ l ∈ L, ∑ m ∈ L, P m * rho * P l = rho := by
      rw [Finset.sum_comm]; exact h1
    rw [h1, h2, ← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℂ, two_smul]
    abel
  have hpsd : (∑ l ∈ L, ∑ m ∈ L, (P l - P m) * rho * (P l - P m)ᴴ).PosSemidef :=
    Matrix.posSemidef_sum _ (fun l _ => Matrix.posSemidef_sum _
      (fun m _ => hrho.1.mul_mul_conjTranspose_same _))
  rw [key] at hpsd
  have := hpsd.smul (show (0 : ℂ) ≤ ((1/2 : ℝ) : ℂ) by exact_mod_cast (by norm_num : (0:ℝ) ≤ 1/2))
  rw [smul_smul] at this
  convert this using 1
  norm_num

end
