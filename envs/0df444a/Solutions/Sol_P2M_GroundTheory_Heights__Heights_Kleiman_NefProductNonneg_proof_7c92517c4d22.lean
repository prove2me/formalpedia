-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_NefProductNonneg_proof_7c92517c4d22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:13.690064+00:00
-- url     : https://prove2.me/submissions/3fd53844-b473-4b5d-9a92-a524c1bf99c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_expand_positions_04d69ef1efbf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_nonneg_of_poly_bf85d1564919
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tpow_1e634deba6a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_twist_276a21fa9e53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tpow_toSubSystem_99110f33f8cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_dim_of_isSubvar_6285aee0eebb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace NefProductNonneg
theorem _root_.solution (hK : VeryAmpleNefPlusAmple.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : NefProductNonneg.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp Ms hW hnef
  obtain ⟨D, hZ⟩ := exists_dim_of_isSubvar hW
  let A : LineBundle k x := twistBundle k x 1
  let c : Finset (Fin e) → ℤ := fun S => bundleNum pp (fun i => if i ∈ S then A else Ms i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin e), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq
    have hK' := fun i => hK k D Ω N x (Ms i) hZ (hnef i) (1 / q) (by positivity)
    choose p m hp hm hva using hK'
    have hpm : ∀ i, (p i : ℤ) = q * m i := by
      intro i
      have h := hm i
      rw [mul_one_div, eq_div_iff hq0.ne'] at h
      have : ((p i : ℤ) : ℚ) = ((q * m i : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hm0 : ∀ i, 0 < m i := by
      intro i
      have : 0 < (q : ℤ) * m i := by rw [← hpm]; exact_mod_cast hp i
      exact pos_of_mul_pos_right this (by positivity)
    let V : Fin e → LineBundle k x := fun i => ((Ms i).tpow (p i)).tensor (twistBundle k x (m i))
    have hV : ∀ i, IsVeryAmple (V i).toSubSystem := by
      intro i
      have : (V i).toSubSystem = twistMul (Ms i).toSubSystem (p i) (m i) := by
        change ((Ms i).tpow (p i)).toSubSystem.twist (twistSys k x (m i)) = _
        rw [LineBundle.tpow_toSubSystem]
        rfl
      rw [this]
      exact hva i
    have hposition : ∀ (L : Fin e → LineBundle k x) (i : Fin e),
        bundleNum pp (Function.update L i (V i)) =
          (q * m i) * bundleNum pp (Function.update L i (Ms i)) +
            m i * bundleNum pp (Function.update L i A) := by
      intro L i
      change bundleNum pp (Function.update L i (((Ms i).tpow (p i)).tensor (twistBundle k x (m i)))) = _
      rw [bundleNum_tensor hR hW, bundleNum_tpow hR hW, ← hpm]
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hm0 i).le
      rw [hn, bundleNum_twist hR hW]
    have hexp := sum_expand_positions (bundleNum pp) V Ms (fun _ => A) (fun i => q * m i) m hposition
    have hVn : 0 ≤ bundleNum pp V := interNum_nonneg_of_veryAmple hR e pp V hW hV
    have hw : ∀ S : Finset (Fin e), (∏ i ∈ S, m i) * (∏ i ∈ Sᶜ, ((q : ℤ) * m i)) =
        (∏ i, m i) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, m i := Finset.prod_pos fun i _ => hm0 i
    rw [hexp] at hVn
    exact (mul_nonneg_iff_of_pos_left hprod).mp hVn
  have h0 := nonneg_of_poly c key
  simpa [c, bundleNum] using h0
end NefProductNonneg
end GroundTheory.Heights₂.Heights.Kleiman
