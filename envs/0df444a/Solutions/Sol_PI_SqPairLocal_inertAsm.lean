-- Prove2me | solution 1 for PI.SqPairLocal.inertAsm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:47:21.702335+00:00
-- url     : https://prove2.me/submissions/894bbeb9-a6f0-4668-b53c-837a020d24b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_mul_nmem
import Theorems.Thm_PI_SqPairLocal_intAt_coe
import Theorems.Thm_PI_SqPairLocal_divAt_of_mem
import Theorems.Thm_PI_SqPairLocal_divAt_trans
import Theorems.Thm_PI_SqPairLocal_pres_of
import Theorems.Thm_PI_SqPairLocal_clear
import Theorems.Thm_PI_SqPairLocal_good_gen
import Theorems.Thm_PI_SqPairLocal_conj_sq
import Theorems.Thm_PI_SqPairLocal_conj_herm
import Theorems.Thm_PI_SqPairLocal_star_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution : InertAsm := by
  unfold InertAsm InertPlace
  intro hLCP hME hD hLM hPL E _ _ _ hE N L' L'' hN hL' hL'' Q hQ hcj c hc
  haveI : Q.IsPrime := hQ.isPrime
  obtain ⟨M⟩ := hME E hE Q hQ hcj
  obtain ⟨G', hG'1, hG'2, hD'⟩ := hD E hE N L' hL' Q hQ hcj
  obtain ⟨G'', hG''1, hG''2, hD''⟩ := hD E hE N L'' hL'' Q hQ hcj
  have hu1 : (G'ᴴ * G'')ᴴ * (G'ᴴ * G'') = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc G' G'ᴴ G'', hG'2, one_mul, hG''1]
  have hu2 : (G'ᴴ * G'') * (G'ᴴ * G'')ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc G'' G''ᴴ G', hG''2, one_mul, hG'1]
  unfold PowLoc at hPL
  obtain ⟨K, hK⟩ := hPL E Q hQ c hc
  obtain ⟨e₁, h1, h2, h3, h4, h5, h6⟩ := hLM E Q hQ M hLCP N hN (G'ᴴ * G'') hu1 hu2 K
  have hϖ : M.ϖ ^ K ∈ Q ^ K := Ideal.pow_mem_pow M.ϖ_Q K
  have tr : ∀ x : E, DivAt Q (M.ϖ ^ K) x → DivAt Q c x := fun x hx => divAt_trans hK hϖ hx
  have hFG' : L'.FG := by
    unfold IsSDG at hL'
    exact hL'.1
  have hFG'' : L''.FG := by
    unfold IsSDG at hL''
    exact hL''.1
  have hA' : G'ᴴ * (G' * e₁ * G'ᴴ) * G' = e₁ := by
    simp only [mul_assoc, hG'1, mul_one]
    rw [← mul_assoc, hG'1, one_mul]
  have hA'' : G''ᴴ * (G' * e₁ * G'ᴴ) * G'' = (G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'') := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [mul_assoc]
  obtain ⟨s', hs', hs'L⟩ := clear hFG'
    (pres_of hG'2 hD' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA']; exact h1 i j))
  obtain ⟨s'', hs'', hs''L⟩ := clear hFG''
    (pres_of hG''2 hD'' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA'']; exact h2 i j))
  obtain ⟨y, i, hi, hyi⟩ := hQ.exists_inv (mul_nmem hs' hs'')
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, t = s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) := ⟨_, rfl⟩
  have ht1 : t - 1 = -(i ^ K) := by
    have hg := geom_sum_mul i K
    linear_combination ht + (∑ k ∈ Finset.range K, i ^ k) * hyi - hg
  have htQ : t - 1 ∈ Q ^ K := by
    rw [ht1]
    exact neg_mem (Ideal.pow_mem_pow hi K)
  have hci : cj E i ∈ Q := by
    have hi' : i ∈ Ideal.comap (cj E) Q := by rw [hcj]; exact hi
    exact hi'
  have hct : cj E t - 1 ∈ Q ^ K := by
    have hc1 : cj E t - 1 = -((cj E i) ^ K) := by
      rw [← map_one (cj E), ← map_sub, ht1, map_neg, map_pow]
    rw [hc1]
    exact neg_mem (Ideal.pow_mem_pow hci K)
  have htc : DivAt Q c ((t : E) - 1) := by
    have h := divAt_of_mem hK htQ
    push_cast at h
    exact h
  have htc' : DivAt Q c (star (t : E) - 1) := by
    rw [star_coe]
    have h := divAt_of_mem hK hct
    push_cast at h
    exact h
  have htc'' : IntAt Q (star (t : E)) := by
    rw [star_coe]
    exact intAt_coe _
  have hE' : G'ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G' = (t : E) • e₁ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hA']
  have hE'' : G''ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G'' =
      (t : E) • ((G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'')) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hA'']
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc
  obtain ⟨a1, a2⟩ := good_gen hG'1 hG'2 hD' hcE h1 (fun i j => tr _ (h3 i j)) (fun i j => tr _ (h5 i j))
    htc htc' htc'' hE'
  obtain ⟨b1, b2⟩ := good_gen hG''1 hG''2 hD'' hcE h2
    (fun i j => by rw [conj_sq (G'ᴴ * G'') e₁ hu2]; exact tr _ (h4 i j))
    (fun i j => by rw [conj_herm (G'ᴴ * G'') e₁ hu1]; exact tr _ (h6 i j))
    htc htc' htc'' hE''
  refine ⟨(t : E) • (G' * e₁ * G'ᴴ), ?_, ?_, ?_⟩
  · unfold Pres
    intro z hz
    have hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) := by
      first
        | exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z
        | (ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])
    rw [hsm,
      show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _,
      ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) =
        (s'' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s' by ring, mul_smul]
    exact L'.smul_mem _ (hs'L z hz)
  · unfold Pres
    intro z hz
    have hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) := by
      first
        | exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z
        | (ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])
    rw [hsm,
      show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _,
      ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) =
        (s' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s'' by ring, mul_smul]
    exact L''.smul_mem _ (hs''L z hz)
  · unfold Good
    exact ⟨a1, b1, a2, b2⟩
end PI.SqPairLocal
