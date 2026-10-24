-- Prove2me | solution 1 for SaturatedNet.Uniqueness.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:50:28.255828+00:00
-- url     : https://prove2.me/submissions/598e00f5-44bc-451d-9971-e16dc92b0423

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix


/- Complete local helper proofs from PositiveWeights.lean. -/

open Matrix

namespace SaturatedNet.Uniqueness.SlackProof

lemma positive_weights {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ) (hv0 : 0 ≤ v)
    (hPv : P *ᵥ v ≤ v) (hpath : ∀ i, ∃ j, Reaches P i j ∧ (P *ᵥ v) j < v j) :
    ∀ i, 0 < v i := by
  have edge : ∀ i j, P i j ≠ 0 → 0 < v j → 0 < v i := by
    intro i j hij hj
    have hp : 0 < P i j := lt_of_le_of_ne (hP i j) (Ne.symm hij)
    have hterm : P i j * v j ≤ (P *ᵥ v) i :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hP i k) (hv0 k)) (Finset.mem_univ j)
    exact (mul_pos hp hj).trans_le (hterm.trans (hPv i))
  have path : ∀ i j, Reaches P i j → 0 < v j → 0 < v i := by
    intro i j hij
    induction hij with
    | refl => exact id
    | @tail j k hij hjk ih => exact fun hk => ih (edge j k hjk hk)
  intro i
  obtain ⟨j, hij, hj⟩ := hpath i
  apply path i j hij
  exact (Finset.sum_nonneg (fun k _ => mul_nonneg (hP j k) (hv0 k))).trans_lt hj

end SaturatedNet.Uniqueness.SlackProof


/- Complete local helper proofs from MaximumPrinciple.lean. -/

open Matrix

namespace SaturatedNet.Uniqueness.SlackProof

lemma subsolution_zero {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ) (hv : ∀ i, 0 < v i)
    (hPv : P *ᵥ v ≤ v) (hpath : ∀ i, ∃ j, Reaches P i j ∧ (P *ᵥ v) j < v j)
    (a : n → ℝ) (ha : 0 ≤ a) (hPa : a ≤ P *ᵥ a) : a = 0 := by
  classical
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have haj : 0 < a j := lt_of_le_of_ne (ha j) (Ne.symm hj)
  have hn : (Finset.univ : Finset n).Nonempty := ⟨j, Finset.mem_univ _⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => a i/v i) hn
  let r := a i/v i
  have hr : 0 < r := (div_pos haj (hv j)).trans_le (hmax j (Finset.mem_univ j))
  have hbound : ∀ j, a j ≤ r*v j := by
    intro j
    exact (div_le_iff₀ (hv j)).mp (hmax j (Finset.mem_univ j))
  have heqi : a i = r*v i := (div_mul_cancel₀ _ (hv i).ne').symm
  have hscale : ∀ k, ∑ j, P k j*(r*v j) = r*(P*ᵥv) k := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrow : ∀ k, (P*ᵥa) k ≤ r*(P*ᵥv) k := by
    intro k
    rw [← hscale]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hP k j))
  have node : ∀ k, a k=r*v k →
      (P*ᵥv) k=v k ∧ ∀ j, P k j≠0 → a j=r*v j := by
    intro k hk
    have heq : (P*ᵥv) k=v k := by
      have hb := (hPa k).trans (hrow k)
      rw [hk] at hb
      exact le_antisymm (hPv k) ((mul_le_mul_iff_right₀ hr).mp hb)
    refine ⟨heq, ?_⟩
    intro j hkj
    apply le_antisymm (hbound j)
    by_contra hn
    have hlt : a j < r*v j := lt_of_not_ge hn
    have hp : 0 < P k j := lt_of_le_of_ne (hP k j) (Ne.symm hkj)
    have hstrict : (P*ᵥa) k < r*(P*ᵥv) k := by
      rw [← hscale]
      exact Finset.sum_lt_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hP k j))
        ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hlt hp⟩
    rw [heq, ← hk] at hstrict
    exact (not_lt_of_ge (hPa k)) hstrict
  obtain ⟨k, hik, hslack⟩ := hpath i
  have heqk : a k=r*v k := by
    clear hslack
    induction hik with
    | refl => exact heqi
    | @tail j k hij hjk ih => exact (node j ih).2 k hjk
  exact (ne_of_lt hslack) (node k heqk).1

end SaturatedNet.Uniqueness.SlackProof


/- Complete local helper proofs from SpectrumBound.lean. -/

open Matrix

namespace SaturatedNet.Uniqueness.SlackProof

lemma spectrum_norm_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ) (hv : ∀ i, 0 < v i)
    (hPv : P *ᵥ v ≤ v) (hpath : ∀ i, ∃ j, Reaches P i j ∧ (P *ᵥ v) j < v j)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) : ‖μ‖ < 1 := by
  let A := P.map (algebraMap ℝ ℂ)
  have heigen : Module.End.HasEigenvalue A.toLin' μ := Module.End.HasEigenvalue.of_mem_spectrum (by
    rwa [Matrix.spectrum_toLin'])
  obtain ⟨z, hz⟩ := heigen.exists_hasEigenvector
  have heq : A *ᵥ z = μ • z := hz.apply_eq_smul
  by_contra hnorm
  have hμge : 1 ≤ ‖μ‖ := le_of_not_gt hnorm
  let a : n → ℝ := fun i => ‖z i‖
  have ha : 0 ≤ a := fun i => norm_nonneg _
  have hPa : a ≤ P*ᵥa := by
    intro i
    have hi : ∑ j, (P i j : ℂ)*z j = μ*z i := congrFun heq i
    calc
      a i ≤ ‖μ‖*‖z i‖ := by dsimp [a]; nlinarith [norm_nonneg (z i)]
      _ = ‖μ*z i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (P i j : ℂ)*z j‖ := congrArg norm hi.symm
      _ ≤ ∑ j, ‖(P i j : ℂ)*z j‖ := norm_sum_le _ _
      _ = (P*ᵥa) i := by
        simp only [Matrix.mulVec, dotProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hP i _), a]
  have hazero := subsolution_zero P hP v hv hPv hpath a ha hPa
  apply hz.2
  funext i
  exact norm_eq_zero.mp (congrFun hazero i)

end SaturatedNet.Uniqueness.SlackProof


open Matrix
open scoped Matrix.Norms.Operator
open SaturatedNet.Uniqueness.SlackProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ) (hv0 : 0 ≤ v) (hv : v ≠ 0)
    (hPv : P *ᵥ v ≤ v) (hpath : ∀ i, ∃ j, Reaches P i j ∧ (P *ᵥ v) j < v j) :
    specRad P < 1 := by
  obtain ⟨i, _⟩ := Function.ne_iff.mp hv
  let : Nonempty n := ⟨i⟩
  have hvpos := positive_weights P hP v hv0 hPv hpath
  apply spectrum.spectralRadius_lt_of_forall_lt (P.map (algebraMap ℝ ℂ))
  intro μ hμ
  exact_mod_cast spectrum_norm_lt_one P hP v hvpos hPv hpath μ hμ


end SaturatedNet.Uniqueness
