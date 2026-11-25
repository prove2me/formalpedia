-- Prove2me | solution 1 for PI.SqPairLocal.small_pert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:34.9971+00:00
-- url     : https://prove2.me/submissions/6cfaf1d2-92e6-4210-822f-06cad67fa10b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_pres_add
import Theorems.Thm_PI_SqPairLocal_pres_sub
import Theorems.Thm_PI_SqPairLocal_pres_mul
import Theorems.Thm_PI_SqPairLocal_pres_smul
import Theorems.Thm_PI_SqPairLocal_pres_conj
import Theorems.Thm_PI_SqPairLocal_coe_cj
import Theorems.Thm_PI_SqPairLocal_smallAt_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Matrix
namespace PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
section Pres
variable {L : Submodule (𝓞 E) (Fin N → E)}
end Pres
section Cj
end Cj
section Small
variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
private lemma smallAt_add' {A B : Matrix (Fin N) (Fin N) E} (hA : SmallAt Q c L A)
    (hB : SmallAt Q c L B) : SmallAt Q c L (A + B) := by
  intro y hy
  obtain ⟨s, hs, m, hm, e1⟩ := hA y hy
  obtain ⟨t, ht, n, hn, e2⟩ := hB y hy
  refine ⟨s * t, fun h => ?_, t • m + s • n, L.add_mem (L.smul_mem t hm) (L.smul_mem s hn), ?_⟩
  · rcases Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› h with h | h
    · exact hs h
    · exact ht h
  · have f1 : (s * t) • (A *ᵥ y) = c • (t • m) := by
      rw [mul_comm, mul_smul, e1, smul_comm]
    have f2 : (s * t) • (B *ᵥ y) = c • (s • n) := by
      rw [mul_smul, e2, smul_comm]
    rw [Matrix.add_mulVec, smul_add, smul_add, f1, f2]
end Small
end PI.SqPairLocal
end
end

set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
namespace PI.SqPairLocal
theorem _root_.solution (hL : IsSDG E N L) {e₀ D : Matrix (Fin N) (Fin N) E} {ρ : 𝓞 E}
    (h₀ : Pres L e₀) (hD : Pres L D) (hρ : Dv Q c ρ) (hρc : Dv Q c (cj E ρ))
    (g1 : SmallAt Q c L (e₀ * e₀ - e₀)) (g2 : SmallAt Q c L (e₀ + e₀ᴴ - 1)) :
    SmallAt Q c L ((e₀ + (ρ : E) • D) * (e₀ + (ρ : E) • D) - (e₀ + (ρ : E) • D)) ∧
      SmallAt Q c L ((e₀ + (ρ : E) • D) + (e₀ + (ρ : E) • D)ᴴ - 1) := by
  have k1 : (e₀ + (ρ : E) • D) * (e₀ + (ρ : E) • D) - (e₀ + (ρ : E) • D) =
      (e₀ * e₀ - e₀) + (ρ : E) • (e₀ * D + D * e₀ - D + (ρ : E) • (D * D)) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
    abel
  have k2 : (e₀ + (ρ : E) • D) + (e₀ + (ρ : E) • D)ᴴ - 1 =
      (e₀ + e₀ᴴ - 1) + (ρ : E) • D + ((cj E ρ : 𝓞 E) : E) • Dᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, coe_cj]
    abel
  have pD : Pres L (e₀ * D + D * e₀ - D + (ρ : E) • (D * D)) :=
    pres_add (pres_sub (pres_add (pres_mul h₀ hD) (pres_mul hD h₀)) hD)
      (pres_smul ρ (pres_mul hD hD))
  refine ⟨?_, ?_⟩
  · rw [k1]
    exact smallAt_add' g1 (smallAt_smul hρ pD)
  · rw [k2]
    exact smallAt_add' (smallAt_add' g2 (smallAt_smul hρ hD))
      (smallAt_smul hρc (pres_conj hL hD))
end PI.SqPairLocal
