-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.finOrdExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:27.382391+00:00
-- url     : https://prove2.me/submissions/b3bbc2f7-47bc-4b01-b1ce-ee88380e0f2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_FinOrdExists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_isSmul_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (hΦ : DVR.PhiFunStatement) (hP : PhiPowStatement) : FinOrdExistsStatement := by
  intro V _ _ _ D F _ _ _ k hk p w hw
  obtain ⟨Φ, hΦr⟩ := hΦ V (maximalIdeal V) D F k hk p w hw
  obtain ⟨c, hc, hcp⟩ := hP V (maximalIdeal V) D F k hk p w hw
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (by omega : 0 < k)
  have hζc : ζ ^ k * c = 1 := by rw [hζ, inv_mul_cancel₀ hc]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_mul] at hζc
    exact zero_ne_one hζc
  refine ⟨ζ, hζ0, k, hk, ?_⟩
  intro ss ts h

  have hpow : (Φ ^ k) (ss 0) = c • ss 0 := by
    have := hcp (fun i => (Φ ^ (i : ℕ)) (ss 0)) (by
      intro i
      rw [hΦr]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at this
    simpa using this
  have key : ∀ n : ℕ, (hn : n ≤ k) → ss ⟨n, by omega⟩ = ζ ^ n • (Φ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := h ⟨n, by omega⟩
      rw [hΦr] at h1
      rw [isSmul_iff] at h2
      have e : ss ⟨n + 1, by omega⟩ = ss (Fin.succ ⟨n, by omega⟩) := rfl
      have e0 : ss ⟨n, by omega⟩ = ss (Fin.castSucc ⟨n, by omega⟩) := rfl
      rw [e, h2, h1, ← e0, ih (by omega), LinearMap.map_smul, smul_smul, pow_succ' ζ n, pow_succ' Φ n,
        Module.End.mul_apply]
  have hlast : ss (Fin.last k) = ss 0 := by
    have := key k le_rfl
    have e : ss (Fin.last k) = ss ⟨k, by omega⟩ := rfl
    rw [e, this, hpow, smul_smul, hζc, one_smul]
  intro α j
  rw [hlast]
end ReciprocityTheory.ChartRestriction.G.H1
