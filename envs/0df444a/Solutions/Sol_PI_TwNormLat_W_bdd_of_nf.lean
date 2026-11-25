-- Prove2me | solution 1 for PI.TwNormLat.W.bdd_of_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:24.986639+00:00
-- url     : https://prove2.me/submissions/c2fd9987-cdd1-4953-b585-8d14c221deb1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_PrXLeOfNf
import Theorems.Thm_PI_TwNormLat_W_fin_split
import Theorems.Thm_PI_TwNormLat_W_intAt_zpow
import Theorems.Thm_PI_TwNormLat_W_intAt_scale
import Theorems.Thm_PI_TwNormLat_W_intAt_add
import Theorems.Thm_PI_TwNormLat_W_intAt_mul
import Theorems.Thm_PI_TwNormLat_W_intAt_natCast
import Theorems.Thm_PI_TwNormLat_W_intAt_pow
import Theorems.Thm_PI_TwNormLat_W_intAt_sub
import Theorems.Thm_PI_TwNormLat_W_intAt_zero
import Theorems.Thm_PI_TwNormLat_W_mem_lam
import Theorems.Thm_PI_TwNormLat_W_mem_stdAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) {N c j : ℕ} (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))
    (n : ℕ → ℤ) (z : Sp E N) (hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) (hz : z ∈ stdAt E N P)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) : Bdd P N c j h := by
  rw [mem_stdAt] at hz
  intro x hx
  rw [mem_lam] at hx
  constructor
  · rw [hc]
    refine ⟨fun l => intAt_sub P (hx _) (intAt_mul P ?_ (hz l)), fun i => intAt_mul P ?_ (hx _)⟩
    · unfold Loc.atN; split_ifs
      · exact hx _
      · exact intAt_zero P
    · rw [← zpow_neg]; exact intAt_zpow P _ (by have := (hn i.1).2; omega)
  · have hv : Crit P N c n z (h x) := by
      rw [← hc]; rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, mem_lam]; exact hx
    have hN : IntAt P (qE P ^ j * Loc.atN (h x) N) := by
      unfold Loc.atN; split_ifs with hN
      · have := hv.2 ⟨0, by omega⟩
        exact intAt_scale P hp (hn 0).1 this
      · simpa using intAt_zero P
    rw [mem_lam]
    intro l
    rw [Pi.smul_apply, smul_eq_mul]
    rcases fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩
    · have e : qE P ^ j * h x (Fin.castAdd c l') = qE P ^ j * (h x (Fin.castAdd c l') - Loc.atN (h x) N * z l') +
          qE P ^ j * Loc.atN (h x) N * z l' := by ring
      rw [e]
      exact intAt_add P (intAt_mul P (intAt_pow P (intAt_natCast P _) _) (hv.1 l')) (intAt_mul P hN (hz l'))
    · exact intAt_scale P hp (hn i.1).1 (hv.2 i)
end PI.TwNormLat.W
