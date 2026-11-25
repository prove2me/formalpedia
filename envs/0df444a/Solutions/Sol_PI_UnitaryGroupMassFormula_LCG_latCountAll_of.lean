-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.latCountAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:14.510954+00:00
-- url     : https://prove2.me/submissions/595e5251-541f-475f-a3fe-41a42c99c654

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_hsN_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_hsN_nonneg
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_gm_spec
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_gm_inj
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_phi_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_amat_sub
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (hB : BoxBound) (hLM : LatMap) (hLS : LatSub) (hS : Sep) (hP : PackLem) (hN : NPos)
    (hC : CardPl) : LatCountAll := by
  classical
  intro I x y hx hy r hr S hSc
  have hn : 1 ≤ I.n := hN I x hx
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hx hy
  have hτx : PI.LatCountG.tau1 I x ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hτy : PI.LatCountG.tau1 I y ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hρle : ∀ v, ρ ≤ Real.sqrt I.n * Real.exp (r v) := fun v => by
    have h0 : ρ ≤ 1 / 2 * (1 / 2) := by rw [hρdef]; exact mul_le_mul hτx hτy hy.le (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.sqrt I.n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have h3 : (1 : ℝ) ≤ Real.exp (r v) := Real.one_le_exp (hr v)
    nlinarith
  let g : I.GFset → (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
    fun γ v => amat I x y v (gm I γ)
  have hgsub : ∀ γ γ' : I.GFset, ∀ v, g γ v - g γ' v = amat I x y v (gm I γ - gm I γ') :=
    fun γ γ' v => (amat_sub I x y v _ _).symm
  have hlat : ∀ γ ∈ S, ∀ u ∈ PI.LatCountG.latSet I y, gm I γ *ᵥ u ∈ PI.LatCountG.latSet I x :=
    fun γ hγ u hu => hLM I x y γ (mem_gf I γ).choose (gm_spec I γ).2 (hSc γ hγ).1 u hu
  have hsep : ∀ γ ∈ S, ∀ γ' ∈ S, gm I γ ≠ gm I γ' → ∃ v, ρ ≤ hsN (g γ v - g γ' v) := by
    intro γ hγ γ' hγ' hne
    have hδ : gm I γ - gm I γ' ≠ 0 := sub_ne_zero.mpr hne
    have hmap : ∀ u ∈ PI.LatCountG.latSet I y,
        (gm I γ - gm I γ') *ᵥ u ∈ PI.LatCountG.latSet I x := by
      intro u hu
      rw [Matrix.sub_mulVec]
      exact hLS I x _ _ (hlat γ hγ u hu) (hlat γ' hγ' u hu)
    have hineq := hS I x y hx hy _ hδ hmap
    rw [← hρdef] at hineq
    by_contra hcon
    push_neg at hcon
    have hprod : ∏ v, hsN (g γ v - g γ' v) < ρ ^ I.f := by
      rw [← hC I, ← Finset.card_univ, ← Finset.prod_const]
      by_cases h0 : ∃ v, hsN (g γ v - g γ' v) = 0
      · obtain ⟨v, hv⟩ := h0
        rw [Finset.prod_eq_zero (Finset.mem_univ v) hv]
        exact Finset.prod_pos fun _ _ => hρ
      · push_neg at h0
        have hne' : (Finset.univ : Finset (InfinitePlace I.F)).Nonempty := by
          by_contra he
          rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at he
          have hf0 : I.f = 0 := by rw [← hC I]; exact Fintype.card_eq_zero
          have hpos : 0 < I.f := by
            first
              | exact (hC I) ▸ Fintype.card_pos
              | unfold Formalism.MainNotions.S.AutInst.f; exact Module.finrank_pos
          omega
        exact Finset.prod_lt_prod_of_nonempty
          (fun v _ => lt_of_le_of_ne (hsN_nonneg _) (h0 v).symm) (fun v _ => hcon v) hne'
    simp only [hgsub] at hprod
    linarith
  have hinj : Set.InjOn g S := by
    intro γ hγ γ' hγ' heq
    by_contra hne
    obtain ⟨v, hv⟩ := hsep γ hγ γ' hγ' (fun h => hne (gm_inj I h))
    rw [heq, sub_self, hsN_zero] at hv
    linarith
  have hbound : ∀ p ∈ S.image g, ∀ v, hsN (p v) ≤ Real.sqrt I.n * Real.exp (r v) := by
    intro p hp v
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    show hsN (amat I x y v (gm I γ)) ≤ _
    rw [← phi_eq]
    refine (hB I.n (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v)).trans ?_
    gcongr
    exact (hSc γ hγ).2 v
  have hsepT : ∀ p ∈ S.image g, ∀ q ∈ S.image g, p ≠ q → ∃ v, ρ ≤ hsN (p v - q v) := by
    intro p hp q hq hpq
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hq
    exact hsep γ hγ γ' hγ' (fun h => hpq (by simp only [g, h]))
  have hpack := hP (InfinitePlace I.F) I.n (fun v => Real.sqrt I.n * Real.exp (r v)) (fun _ => ρ)
    (fun _ => hρ) (fun v => by positivity) (S.image g) hbound hsepT
  have hexp : ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) = Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnn : ∀ v, 0 ≤ 2 * (Real.sqrt I.n * Real.exp (r v)) + ρ := fun v => by
    have := Real.sqrt_nonneg (I.n : ℝ)
    have := Real.exp_pos (r v)
    nlinarith
  calc (S.card : ℝ) = ((S.image g).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∏ v, ((2 * (Real.sqrt I.n * Real.exp (r v)) + ρ) / ρ) ^ (2 * I.n ^ 2) := hpack
    _ ≤ ∏ v, ((3 * Real.sqrt I.n / ρ) * Real.exp (r v)) ^ (2 * I.n ^ 2) := by
        refine Finset.prod_le_prod (fun v _ => pow_nonneg (div_nonneg (hnn v) hρ.le) _)
          (fun v _ => ?_)
        refine pow_le_pow_left₀ (div_nonneg (hnn v) hρ.le) ?_ _
        rw [div_mul_eq_mul_div]
        gcongr
        nlinarith [hρle v]
    _ = (∏ v : InfinitePlace I.F, (3 * Real.sqrt I.n / ρ) ^ (2 * I.n ^ 2)) *
          ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) := by
        rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]
    _ = _ := by rw [hexp, Finset.prod_const, Finset.card_univ, hC I, ← pow_mul]
end PI.UnitaryGroupMassFormula.LCG
