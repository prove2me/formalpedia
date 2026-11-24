-- Prove2me | solution 1 for ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:43:30.566596+00:00
-- url     : https://prove2.me/submissions/084d04b7-4d79-4068-95bd-0d16791e3500

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
open Set


theorem solution (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) := by
  classical
  let A (n : ℕ) := Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n}
  let f (n : ℕ) : ℂ := (A n : ℂ)
  have hnz := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT E).eventually_ne
    (Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero E))
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 1, r < s := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)
  obtain ⟨r, hr, hz⟩ := (hlt.and hnz).exists
  have hsum : LSeriesSummable f (r:ℂ) := by
    by_contra bad
    apply hz
    have hzero : NumberField.dedekindZeta E (r : ℂ) = 0 := tsum_eq_zero_of_not_summable bad
    simp [hzero]
  have H : LSeriesSummable f (s:ℂ) := hsum.of_re_le_re (by simpa using hr.le)
  have Hn : Summable (fun n : ℕ => (A n : ℝ) * (n : ℝ) ^ (-s)) := by
    apply H.norm.congr; intro n
    rw [LSeries.norm_term_eq]; by_cases hn : n = 0
    · subst n; simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    · simp [hn,f,Real.rpow_neg (Nat.cast_nonneg _),div_eq_mul_inv]
  refine summable_of_sum_le (c := idealZetaR E s) (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
  intro T
  let N : Ideal (𝓞 E) → ℕ := Ideal.absNorm
  let v (n : ℕ) := (n : ℝ) ^ (-s)
  calc
    _ = ∑ n ∈ T.image N, ∑ I ∈ T.filter (fun I => N I = n), v (N I) :=
      (Finset.sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem N) _).symm
    _ ≤ ∑ n ∈ T.image N, (A n : ℝ) * v n := by
      apply Finset.sum_le_sum; intro n _
      let S := T.filter (fun I => N I = n)
      have hsub (I) (hI : I ∈ S) : N I = n := (Finset.mem_filter.mp hI).2
      haveI : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      have hc : S.card ≤ A n := by
        let g : S → {I : Ideal (𝓞 E) // Ideal.absNorm I = n} := fun I => ⟨I.1, hsub _ I.2⟩
        simpa [A] using Nat.card_le_card_of_injective g (fun a b h => Subtype.ext (congrArg (fun I : {I : Ideal (𝓞 E) // Ideal.absNorm I = n} => I.val) h))
      calc
        _ = ∑ _I ∈ S, v n := Finset.sum_congr rfl (fun I hI => congrArg v (hsub I hI))
        _ = (S.card : ℝ) * v n := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := Hn.sum_le_tsum _ (fun n _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
