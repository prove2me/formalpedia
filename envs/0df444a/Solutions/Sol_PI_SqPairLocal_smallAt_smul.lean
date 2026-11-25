-- Prove2me | solution 1 for PI.SqPairLocal.smallAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:11.115528+00:00
-- url     : https://prove2.me/submissions/cbb9b5e8-e90b-46eb-8840-a10b63db42e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
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
private lemma integers_smul_eq_coe_smul (r : 𝓞 E) (v : Fin N → E) : r • v = (r : E) • v := by
  first
    | exact (algebraMap_smul E r v).symm
    | rfl
    | (ext i; simp [Algebra.smul_def])
private lemma smul_mulVec_eq_smul (a : E) (A : Matrix (Fin N) (Fin N) E) (b : Fin N → E) :
    (a • A) *ᵥ b = a • (A *ᵥ b) := by
  first
    | exact Matrix.smul_mulVec a A b
    | exact Matrix.smul_mulVec_assoc a A b
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
end Pres
section Cj
end Cj
section Small
variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
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
theorem _root_.solution {ρ : 𝓞 E} {X : Matrix (Fin N) (Fin N) E} (hρ : Dv Q c ρ) (hX : Pres L X) :
    SmallAt Q c L ((ρ : E) • X) := by
  intro y hy
  obtain ⟨s, hs, w, hw⟩ := hρ
  refine ⟨s, hs, w • (X *ᵥ y), L.smul_mem w (hX y hy), ?_⟩
  have hw' : (s : E) * (ρ : E) = (c : E) * (w : E) := by
    first
      | exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hw
      | simpa using congrArg (fun t : 𝓞 E => (t : E)) hw
  simp only [integers_smul_eq_coe_smul]
  rw [smul_mulVec_eq_smul, smul_smul, smul_smul, hw']
end PI.SqPairLocal
