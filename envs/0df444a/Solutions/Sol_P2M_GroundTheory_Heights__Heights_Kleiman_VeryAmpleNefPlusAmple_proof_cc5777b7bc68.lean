-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleNefPlusAmple_proof_cc5777b7bc68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:07.638026+00:00
-- url     : https://prove2.me/submissions/6eeb36f0-dbdb-456d-a7c9-77aff3fb6132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_f2603d4882c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_twistMul_one_zero_75731c337a9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_upward_594d791661c9

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
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleNefPlusAmple
theorem _root_.solution (hGen : Generated.Statement.{u, w})
    (hSec : SectionExists.Statement.{u, w}) (hThree : StepThree.Statement.{u, w})
    (hJ : GraphClosed.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    VeryAmpleNefPlusAmple.Statement.{u, w} := by
  intro k _ d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  rcases d with _ | d
  · intro Ω _ _ N x M hdim _ t ht
    have hG : (twistMul M.toSubSystem 1 0).Generated := by
      rw [KThm.twistMul_one_zero]; exact hPt k Ω N x M hdim
    exact KThm.upward hJ M 1 0 le_rfl hG t (by push_cast; linarith)
  · intro Ω _ _ N x M hdim hnef

    let VA : ℚ → Prop := fun u =>
      ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * u ∧ IsVeryAmple (twistMul M.toSubSystem p m)
    set ρ : ℚ := 1 - 1 / (2 * ((d : ℚ) + 1)) with hρ
    have hd : (0 : ℚ) < (d : ℚ) + 1 := by positivity
    have hρ0 : 0 < ρ := by
      rw [hρ]
      have : 1 / (2 * ((d : ℚ) + 1)) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have : (0 : ℚ) ≤ d := by positivity
        linarith
      linarith
    have hρ1 : ρ < 1 := by
      rw [hρ]
      have : 0 < 1 / (2 * ((d : ℚ) + 1)) := by positivity
      linarith

    have step : ∀ u : ℚ, 0 < u → VA u → ∀ t'' : ℚ, u * ρ < t'' → VA t'' := by
      intro u hu hVA t'' ht''
      have hs'0 : 0 < u / (2 * ((d : ℚ) + 1)) := by positivity
      have hs'lt : u / (2 * ((d : ℚ) + 1)) < u / ((d : ℚ) + 1) := by
        apply div_lt_div_of_pos_left hu hd; linarith
      obtain ⟨p, m, c₁, hp, hm, hc₁, σ, hσ, hσ0⟩ :=
        hSec k Ω N x d M u (u / (2 * ((d : ℚ) + 1))) hdim hnef hs'0 (by exact_mod_cast hs'lt) hVA
      let T : StepData k x :=
        { d := d, dim := hdim, M := M, nef := hnef, t := u, s' := u / (2 * ((d : ℚ) + 1)),
          s'_pos := hs'0, s'_lt := by exact_mod_cast hs'lt, p := p, p_pos := hp, m := m, m_eq := hm,
          c₁ := c₁, c₁_pos := hc₁, si := σ, si_mem := hσ, si_ne := hσ0 }
      obtain ⟨c₂, hc₂⟩ := hThree k Ω N x T (fun e he => ih e (Nat.lt_succ_of_le he))
      have hδ : 0 < t'' - (u - u / (2 * ((d : ℚ) + 1))) := by
        have : u * ρ = u - u / (2 * ((d : ℚ) + 1)) := by rw [hρ]; ring
        linarith
      obtain ⟨n, hn⟩ := exists_nat_gt ((c₂ : ℚ) / (t'' - (u - u / (2 * ((d : ℚ) + 1)))))
      have hgen := hc₂ (n + 1) (by omega)
      have heq : (T.L.pow (n + 1)).twist (twistSys k x c₂) =
          twistMul M.toSubSystem (p * (n + 1)) (m * (n + 1) + c₂) := by
        refine SubSystem.ext_sub fun I => ?_
        obtain ⟨i, hi⟩ := I.2.1
        rw [KThm.sub_twist, KThm.sub_pow, show T.L = twistMul M.toSubSystem p m from rfl,
          KThm.sub_twistMul _ _ _ I hi, KThm.sub_twistMul _ _ _ I hi]
        change twistMod k x c₂ I * _ = _
        rw [twistMod_eq_span _ I hi, mul_pow, ← pow_mul, KThm.span_zpow_pow I hi, mul_left_comm,
          KThm.span_zpow_mul I hi]
        congr 3
        push_cast; ring_nf
      rw [heq] at hgen
      refine KThm.upward hJ M (p * (n + 1)) (m * (n + 1) + c₂) (by nlinarith) hgen t'' ?_
      have hc₂lt : (c₂ : ℚ) < n * (t'' - (u - u / (2 * ((d : ℚ) + 1)))) := by
        rwa [div_lt_iff₀ hδ] at hn
      have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
      have hn0 : (0 : ℚ) ≤ n := by positivity
      have h1 : (n : ℚ) * (t'' - (u - u / (2 * ((d : ℚ) + 1)))) ≤
          p * ((n : ℚ) + 1) * (t'' - (u - u / (2 * ((d : ℚ) + 1)))) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hδ.le
      push_cast
      rw [hm]
      linarith

    obtain ⟨c₀, hc₀⟩ := hGen k Ω N x M
    have base : ∀ t : ℚ, (c₀ : ℚ) < t → VA t := fun t ht =>
      KThm.upward hJ M 1 c₀ le_rfl (by rw [KThm.twistMul_one]; exact hc₀ c₀ le_rfl) t
        (by push_cast; linarith)
    have iter : ∀ n : ℕ, ∀ t : ℚ, |(c₀ : ℚ)| * ρ ^ n < t → VA t := by
      intro n
      induction n with
      | zero =>
        intro t ht
        exact base t (by have := le_abs_self (c₀ : ℚ); simp at ht; linarith)
      | succ n ihn =>
        intro t ht
        have ha : 0 ≤ |(c₀ : ℚ)| * ρ ^ n := by positivity
        have hat : |(c₀ : ℚ)| * ρ ^ n * ρ < t := by rw [pow_succ, ← mul_assoc] at ht; exact ht
        have htρ : |(c₀ : ℚ)| * ρ ^ n < t / ρ := by rw [lt_div_iff₀ hρ0]; exact hat
        set a := |(c₀ : ℚ)| * ρ ^ n
        have hu0 : 0 < (a + t / ρ) / 2 := by linarith
        refine step ((a + t / ρ) / 2) hu0 (ihn _ (by linarith)) t ?_
        have : (a + t / ρ) / 2 < t / ρ := by linarith
        rwa [lt_div_iff₀ hρ0] at this
    intro t ht
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos ht (by positivity : (0 : ℚ) < |(c₀ : ℚ)| + 1)) hρ1
    refine iter n t ?_
    have hpos : 0 ≤ ρ ^ n := by positivity
    rw [lt_div_iff₀ (by positivity)] at hn
    nlinarith [abs_nonneg (c₀ : ℚ)]
end VeryAmpleNefPlusAmple
end GroundTheory.Heights₂.Heights.Kleiman
