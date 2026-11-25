-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.twisted_eisenstein_of_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:29.178198+00:00
-- url     : https://prove2.me/submissions/9b71a439-ab3a-4ffb-88f0-71fb9b712660

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfHypotheses
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_core

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
theorem _root_.solution (hStab : StabP) (hCoV : CoVP) (hOm : OmStepP) (hPS : PhiSuppP) (hPP : PhiPerP)
    (hBE : BddEntP) (hGS : GSuppP) (hGP : GPerP) (hHG : HGoodP) (hCB : ChArgBddP) (hXX : XXP)
    (hTA : TrAffP) (hRX : ResXSurjP) (hCA : ChArgP) : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing := by
  intro E K _ _ _ _ R P hp hq psi sq cq ξ hpsi hsq hcq i hi hal h h' hbal hbh hbh' hdc hne
  obtain ⟨r, hr, κ, hκ, rfl⟩ := hdc
  have m1 : i ≤ i * (R.t + 1) := Nat.le_mul_of_pos_right i (Nat.succ_pos _)
  have m2 : i + 1 ≤ (i + 1) * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hk := R.m_add_three_le_k
  have s1 : R.r = (R.k + (i + 1)) + cOf R (i + 1) := by
    unfold Ranks.r cOf
    omega
  have s3 : R.k + (i + 1) ≤ R.N (i + 1) := by
    unfold Ranks.N
    omega
  have s4 : R.r ≤ R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    omega
  have s5 : R.k ≤ R.N i := by
    unfold Ranks.N
    omega
  have s6 : R.k ≤ R.N (i + 1) := by
    unfold Ranks.N
    omega
  have s7 : cOf R (i + 1) < cOf R i := by
    unfold cOf
    omega
  by_cases hq0 : ((qOf P : ℕ) : K) = 0
  · exfalso
    have hFC : Nonempty (FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) :=
      ⟨⟨(⟨0, by omega⟩, ⟨R.N i + cOf R (i + 1), by omega⟩), by
        show IsFree (R.N i) (R.N (i + 1)) (cOf R (i + 1)) 0 (R.N i + cOf R (i + 1))
        unfold IsFree
        omega⟩⟩
    obtain ⟨A0, B0, hAB⟩ := hne
    refine hAB A0 (B0 + 1) le_rfl (Nat.le_succ _) ?_
    funext xj
    show (((qOf P : K) ^ (B0 + 1))⁻¹) ^ Fintype.card (FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) * _ = 0
    rw [hq0, zero_pow (Nat.succ_ne_zero _), inv_zero, zero_pow Fintype.card_ne_zero, zero_mul]
  have hρ : r⁻¹ ∈ R1 E (R.N (i + 1)) (cOf R (i + 1)) := inv_mem hr
  obtain ⟨C, hC, hCeq⟩ := hOm E K P hp hq sq cq hsq hcq ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
    (R.k + (i + 1)) s1 (Nat.le_add_right _ _) s3 s4 s5 hal h r κ hκ
  obtain ⟨bh1, bh2⟩ := hBE E P R (i + 1) h hbh
  obtain ⟨bh1', -⟩ := hBE E P R (i + 1) (r * h * κ) hbh'
  obtain ⟨ba1, ba2⟩ := hBE E P R i hal hbal
  have hPhiS := hPS E K P (qOf P) ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) s6 s5
  have hPhiP := hPP E K P hp hq ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
  have gS := hGS E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal h _ (i + 1) hPhiS ba2 bh1
  have gS' := hGS E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal (r * h * κ) _ (i + 1) hPhiS ba2 bh1'
  have gP := hGP E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal h _ i hPhiP ba1 bh2
  have hHg := hHG E K P hp (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) (2 * R.m) (i + 1) (by omega) psi hpsi _ gS gP
  exact core P hp hq hq0 hStab hCoV hXX hTA hRX hCA hCB (D := 2 * R.m) (j := i + 1) (by omega) hpsi _ _ r⁻¹ hρ
    C hC hCeq gS gS' hHg hne
end PI.TwistedEisensteinNonvanishing.W
