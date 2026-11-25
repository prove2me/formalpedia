-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:46.081108+00:00
-- url     : https://prove2.me/submissions/9867a405-c9a8-409f-9330-c9da80b68870

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfHypotheses
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_psi_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_key_pt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_RS_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hq0 : ((qOf P : ℕ) : K) ≠ 0) (hStab : StabP) (hCoV : CoVP) (hXX : XXP) (hTA : TrAffP)
    (hRX : ResXSurjP) (hCA : ChArgP) (hCB : ChArgBddP)
    {n' c' n c D j : ℕ} (hjD : j ≤ D) {psi : E → K} (hpsi : PsiOk D P psi)
    (G G' : SF E K (n' + c') (n + c)) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (hρ : ρ ∈ R1 E n c)
    (C : K) (hC : C ≠ 0) (hCeq : ∀ x, G' x = C * G (ρ.toLinearMap ∘ₗ x))
    (hS : ∀ x, G x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hS' : ∀ x, G' x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hH : ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      Good P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))))
    (hne : ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0) :
    ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0 := by
  obtain ⟨L, hL⟩ := hTA E n' c' n c ρ hρ
  obtain ⟨cT, hcT, hcov⟩ := hCoV E K P hp hq hq0 (FC n' c' n c) L (Tr ρ 0)
  obtain ⟨a', b', hab⟩ := hcov j j
  have key : ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      G' (xx1 xj t) * psi (-chArg (xx1 xj t)) =
        (C * psi (chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E)))) *
          (G (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)) * psi (-chArg (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)))) := by
    intro xj t
    have e1 : ρ.toLinearMap ∘ₗ xx1 xj t = xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0) := by
      rw [hXX E n' c' n c ρ hρ xj t, hL t]
    rw [← e1]
    exact key_pt hjD hpsi hC (hCeq _) (hCA E n' c' n c ρ hρ xj t)
      (fun h0 => hCB E P n' c' n c j _ (hS' _ h0)) (fun h0 => hCB E P n' c' n c j _ (hS _ h0))
  obtain ⟨A0, B0, hAB⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      RS P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))) ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (hAB (max A0 j) (max B0 j) (le_max_left _ _) (le_max_left _ _))
    refine ⟨y, ?_⟩
    simp only [Pi.zero_apply] at hy
    rwa [← hStab E K P hp hq hq0 _ j j _ (hH y) _ _ (le_max_right _ _) (le_max_right _ _)]
  obtain ⟨xj, rfl⟩ := hRX E n' n c ρ hρ y
  obtain ⟨hg, heq⟩ := hab _ (hH (resX ρ ∘ₗ xj))
  refine ⟨a', b', fun A' B' hA' hB' hz => ?_⟩
  have h1 := congrFun hz xj
  simp only [Pi.zero_apply] at h1
  rw [show (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t))) = fun t =>
      (C * psi (chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E)))) *
        (G (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)) * psi (-chArg (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0))))
      from funext (key xj), RS_mul, hStab E K P hp hq hq0 _ a' b' _ hg A' B' hA' hB', heq] at h1
  exact mul_ne_zero (mul_ne_zero hC (psi_ne hpsi _)) (mul_ne_zero hcT hy) h1
end PI.TwistedEisensteinNonvanishing.W
