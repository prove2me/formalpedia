-- Prove2me | solution 1 for PI.KerIso.DetOrdW.val_det_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:45.617667+00:00
-- url     : https://prove2.me/submissions/9a047186-aa78-4c25-b7ef-794d8004aa77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
import Theorems.Thm_PI_KerIso_DetOrdW_val_le_one_of_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerIso PI.KerIso.DetOrdW
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace PI.KerIso.DetOrdW
theorem _root_.solution (𝔭 : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : (ι → K) →ₗ[K] (ι → K))
    (hu : ∀ v : ι → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
      ∃ s : ℕ, Nat.Coprime s p ∧ ∀ w, (s : K) * u v w ∈ (algebraMap (𝓞 K) K).range) :
    𝔭.valuation K (LinearMap.det u) ≤ 1 := by
  set M := LinearMap.toMatrix' u with hM
  have hsingle : ∀ j : ι, ∀ w, (Pi.single j (1 : K) : ι → K) w ∈ (algebraMap (𝓞 K) K).range := by
    intro j w
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  choose s hs hsi using fun j => hu (Pi.single j 1) (hsingle j)
  have hent : ∀ i j, M i j * (s j : K) ∈ (algebraMap (𝓞 K) K).range := by
    intro i j
    rw [hM, LinearMap.toMatrix'_apply, mul_comm]
    exact hsi j i
  choose N hN using fun i j => hent i j
  have hdet : LinearMap.det u * ((∏ j, s j : ℕ) : K) = algebraMap (𝓞 K) K (Matrix.of N).det := by
    rw [RingHom.map_det, ← LinearMap.det_toMatrix', ← hM, Nat.cast_prod, ← Matrix.det_diagonal, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_diagonal, hN]
  apply val_le_one_of_den 𝔭 hp (Nat.Coprime.prod_left fun j _ => hs j)
  rw [mul_comm, hdet]
  exact RingHom.mem_range_self _ _
end PI.KerIso.DetOrdW
