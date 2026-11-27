-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormFormDvd_proof_c6a939978026
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:07.645484+00:00
-- url     : https://prove2.me/submissions/35626f87-40fd-446d-9ddc-dcc470d55753

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormFormDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace NormFormDvd
theorem _root_.solution (h₁ : NormFormEmbeddings.Statement) (h₂ : LinearFormPrime.Statement)
    (h₃ : MapDvdDescent.Statement) : NormFormDvd.Statement := by
  intro K L _ _ _ _ _ _ n η t P hgen ht hdvd
  classical
  apply h₃ K (AlgebraicClosure K) (Fin n)
  rw [h₁ K L (AlgebraicClosure K) n η]
  set θ : (L →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin n) (AlgebraicClosure K) :=
    fun σ => ∑ m, X m * C (σ (η m)) with hθ

  have hev : ∀ σ, eval (fun m => algebraMap K (AlgebraicClosure K) (t m)) (θ σ) = 1 := by
    intro σ
    have h := congrArg σ ht
    simp only [map_sum, map_one, Algebra.smul_def, map_mul, AlgHom.commutes] at h
    simpa [hθ, map_sum, mul_comm] using h

  have hcoord : ∀ σ m, eval (Pi.single m 1) (θ σ) = σ (η m) := by
    intro σ m
    simp [hθ, Pi.single_apply]
  have hprime : ∀ σ, Prime (θ σ) := by
    intro σ
    refine h₂ (AlgebraicClosure K) n (fun m => σ (η m)) ?_
    intro h0
    have h := hev σ
    have hz : θ σ = 0 := by simp only [hθ]; simp [funext_iff] at h0; simp [h0]
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hdiv : ∀ σ, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro σ
    obtain ⟨Q, hQ⟩ := hdvd
    refine ⟨map (σ : L →+* AlgebraicClosure K) Q, ?_⟩
    have h := congrArg (map (σ : L →+* AlgebraicClosure K)) hQ
    rw [map_map, AlgHom.comp_algebraMap, map_mul] at h
    rw [h]
    congr 1
    simp [hθ, map_sum]
  have hinj : ∀ a b, θ a ∣ θ b → a = b := by
    intro a b hab
    obtain ⟨u, hu⟩ := (hprime a).associated_of_dvd (hprime b) hab
    obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    rw [hc] at hu
    have h1 := congrArg (eval (fun m => algebraMap K (AlgebraicClosure K) (t m))) hu
    rw [eval_mul, hev, hev, eval_C, one_mul] at h1
    rw [h1, C_1, mul_one] at hu
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    rintro _ ⟨m, rfl⟩
    rw [← hcoord a m, ← hcoord b m, hu]
  have key : ∀ s : Finset (L →ₐ[K] AlgebraicClosure K),
      ∏ σ ∈ s, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨R, hR⟩ := ih
      have h := hdiv a
      rw [hR] at h
      rcases (hprime a).dvd_or_dvd h with h' | h'
      · exfalso
        obtain ⟨b, hb, hab⟩ := ((hprime a).dvd_finsetProd_iff _).1 h'
        exact ha (by rw [hinj a b hab]; exact hb)
      · obtain ⟨S, hS⟩ := h'
        exact ⟨S, by rw [hR, hS]; ring⟩
  exact key Finset.univ
end NormFormDvd
end GroundTheory.Heights₂.Heights
